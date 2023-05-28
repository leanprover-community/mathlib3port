/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz

! This file was ported from Lean 3 source module algebraic_topology.simplicial_object
! leanprover-community/mathlib commit 814d76e2247d5ba8bc024843552da1278bfe9e5c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicTopology.SimplexCategory
import Mathbin.CategoryTheory.Arrow
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Opposites

/-!
# Simplicial objects in a category.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A simplicial object in a category `C` is a `C`-valued presheaf on `simplex_category`.
(Similarly a cosimplicial object is functor `simplex_category ⥤ C`.)

Use the notation `X _[n]` in the `simplicial` locale to obtain the `n`-th term of a
(co)simplicial object `X`, where `n` is a natural number.

-/


open Opposite

open CategoryTheory

open CategoryTheory.Limits

universe v u v' u'

namespace CategoryTheory

variable (C : Type u) [Category.{v} C]

#print CategoryTheory.SimplicialObject /-
/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `simplex_category` to `C`. -/
@[nolint has_nonempty_instance]
def SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C deriving Category
#align category_theory.simplicial_object CategoryTheory.SimplicialObject
-/

namespace SimplicialObject

-- mathport name: simplicial_object.at
scoped[Simplicial]
  notation:1000 X " _[" n "]" =>
    (X : CategoryTheory.SimplicialObject hole!).obj (Opposite.op (SimplexCategory.mk n))

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject C) := by dsimp [simplicial_object]; infer_instance

instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject C) := by dsimp [simplicial_object]; infer_instance

instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C} (X : SimplicialObject C)

/- warning: category_theory.simplicial_object.δ -> CategoryTheory.SimplicialObject.δ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ CategoryTheory.SimplicialObject.δₓ'. -/
/-- Face maps for a simplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.δ i).op
#align category_theory.simplicial_object.δ CategoryTheory.SimplicialObject.δ

/- warning: category_theory.simplicial_object.σ -> CategoryTheory.SimplicialObject.σ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.σ CategoryTheory.SimplicialObject.σₓ'. -/
/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.σ i).op
#align category_theory.simplicial_object.σ CategoryTheory.SimplicialObject.σ

/- warning: category_theory.simplicial_object.eq_to_iso -> CategoryTheory.SimplicialObject.eqToIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} {m : Nat}, (Eq.{1} Nat n m) -> (CategoryTheory.Iso.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk m))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} {m : Nat}, (Eq.{1} Nat n m) -> (CategoryTheory.Iso.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk m))))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.eq_to_iso CategoryTheory.SimplicialObject.eqToIsoₓ'. -/
/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (eqToIso (by rw [h]))
#align category_theory.simplicial_object.eq_to_iso CategoryTheory.SimplicialObject.eqToIso

/- warning: category_theory.simplicial_object.eq_to_iso_refl -> CategoryTheory.SimplicialObject.eqToIso_refl is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} (h : Eq.{1} Nat n n), Eq.{succ u1} (CategoryTheory.Iso.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (CategoryTheory.SimplicialObject.eqToIso.{u1, u2} C _inst_1 X n n h) (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} (h : Eq.{1} Nat n n), Eq.{succ u1} (CategoryTheory.Iso.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (CategoryTheory.SimplicialObject.eqToIso.{u1, u2} C _inst_1 X n n h) (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.eq_to_iso_refl CategoryTheory.SimplicialObject.eqToIso_reflₓ'. -/
@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by ext; simp [eq_to_iso]
#align category_theory.simplicial_object.eq_to_iso_refl CategoryTheory.SimplicialObject.eqToIso_refl

/- warning: category_theory.simplicial_object.δ_comp_δ -> CategoryTheory.SimplicialObject.δ_comp_δ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_δ CategoryTheory.SimplicialObject.δ_comp_δₓ'. -/
/-- The generic case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j := by dsimp [δ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.simplicial_object.δ_comp_δ CategoryTheory.SimplicialObject.δ_comp_δ

/- warning: category_theory.simplicial_object.δ_comp_δ' -> CategoryTheory.SimplicialObject.δ_comp_δ' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_δ' CategoryTheory.SimplicialObject.δ_comp_δ'ₓ'. -/
@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.cast_succ < j) :
    X.δ j ≫ X.δ i =
      X.δ i.cast_succ ≫ X.δ (j.pred fun hj => by simpa only [hj, Fin.not_lt_zero] using H) :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.simplicial_object.δ_comp_δ' CategoryTheory.SimplicialObject.δ_comp_δ'

/- warning: category_theory.simplicial_object.δ_comp_δ'' -> CategoryTheory.SimplicialObject.δ_comp_δ'' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_δ'' CategoryTheory.SimplicialObject.δ_comp_δ''ₓ'. -/
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ j.cast_succ) :
    X.δ j.succ ≫ X.δ (i.cast_lt (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.simplicial_object.δ_comp_δ'' CategoryTheory.SimplicialObject.δ_comp_δ''

/- warning: category_theory.simplicial_object.δ_comp_δ_self -> CategoryTheory.SimplicialObject.δ_comp_δ_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_δ_self CategoryTheory.SimplicialObject.δ_comp_δ_selfₓ'. -/
/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : X.δ i.cast_succ ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self CategoryTheory.SimplicialObject.δ_comp_δ_self

/- warning: category_theory.simplicial_object.δ_comp_δ_self' -> CategoryTheory.SimplicialObject.δ_comp_δ_self' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_δ_self' CategoryTheory.SimplicialObject.δ_comp_δ_self'ₓ'. -/
@[reassoc]
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = i.cast_succ) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by subst H; rw [δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self' CategoryTheory.SimplicialObject.δ_comp_δ_self'

/- warning: category_theory.simplicial_object.δ_comp_σ_of_le -> CategoryTheory.SimplicialObject.δ_comp_σ_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_σ_of_le CategoryTheory.SimplicialObject.δ_comp_σ_of_leₓ'. -/
/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.cast_succ) :
    X.σ j.succ ≫ X.δ i.cast_succ = X.δ i ≫ X.σ j := by dsimp [δ, σ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.simplicial_object.δ_comp_σ_of_le CategoryTheory.SimplicialObject.δ_comp_σ_of_le

/- warning: category_theory.simplicial_object.δ_comp_σ_self -> CategoryTheory.SimplicialObject.δ_comp_σ_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_σ_self CategoryTheory.SimplicialObject.δ_comp_σ_selfₓ'. -/
/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.cast_succ = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_self CategoryTheory.SimplicialObject.δ_comp_σ_self

/- warning: category_theory.simplicial_object.δ_comp_σ_self' -> CategoryTheory.SimplicialObject.δ_comp_σ_self' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_σ_self' CategoryTheory.SimplicialObject.δ_comp_σ_self'ₓ'. -/
@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.cast_succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by subst H; rw [δ_comp_σ_self]
#align category_theory.simplicial_object.δ_comp_σ_self' CategoryTheory.SimplicialObject.δ_comp_σ_self'

/- warning: category_theory.simplicial_object.δ_comp_σ_succ -> CategoryTheory.SimplicialObject.δ_comp_σ_succ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.SimplicialObject.σ.{u1, u2} C _inst_1 X n i) (CategoryTheory.SimplicialObject.δ.{u1, u2} C _inst_1 X n (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i))) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.SimplicialObject.σ.{u1, u2} C _inst_1 X n i) (CategoryTheory.SimplicialObject.δ.{u1, u2} C _inst_1 X n (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i))) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_σ_succ CategoryTheory.SimplicialObject.δ_comp_σ_succₓ'. -/
/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_succ CategoryTheory.SimplicialObject.δ_comp_σ_succ

/- warning: category_theory.simplicial_object.δ_comp_σ_succ' -> CategoryTheory.SimplicialObject.δ_comp_σ_succ' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} {j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))}, (Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) j (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i)) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.SimplicialObject.σ.{u1, u2} C _inst_1 X n i) (CategoryTheory.SimplicialObject.δ.{u1, u2} C _inst_1 X n j)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) {n : Nat} {j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))}, (Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) j (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i)) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n))) (CategoryTheory.SimplicialObject.σ.{u1, u2} C _inst_1 X n i) (CategoryTheory.SimplicialObject.δ.{u1, u2} C _inst_1 X n j)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.CategoryStruct.toQuiver.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.toCategoryStruct.{0, 0} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory))) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} (Opposite.{1} SimplexCategory) (CategoryTheory.Category.opposite.{0, 0} SimplexCategory SimplexCategory.smallCategory) C _inst_1 X) (Opposite.op.{1} SimplexCategory (SimplexCategory.mk n)))))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_σ_succ' CategoryTheory.SimplicialObject.δ_comp_σ_succ'ₓ'. -/
@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by subst H; rw [δ_comp_σ_succ]
#align category_theory.simplicial_object.δ_comp_σ_succ' CategoryTheory.SimplicialObject.δ_comp_σ_succ'

/- warning: category_theory.simplicial_object.δ_comp_σ_of_gt -> CategoryTheory.SimplicialObject.δ_comp_σ_of_gt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_σ_of_gt CategoryTheory.SimplicialObject.δ_comp_σ_of_gtₓ'. -/
/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.cast_succ < i) :
    X.σ j.cast_succ ≫ X.δ i.succ = X.δ i ≫ X.σ j := by dsimp [δ, σ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt CategoryTheory.SimplicialObject.δ_comp_σ_of_gt

/- warning: category_theory.simplicial_object.δ_comp_σ_of_gt' -> CategoryTheory.SimplicialObject.δ_comp_σ_of_gt' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_comp_σ_of_gt' CategoryTheory.SimplicialObject.δ_comp_σ_of_gt'ₓ'. -/
@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred fun hi => by simpa only [Fin.not_lt_zero, hi] using H) ≫
        X.σ
          (j.cast_lt
            ((add_lt_add_iff_right 1).mp
              (lt_of_lt_of_le
                (by simpa only [[anonymous], ← Fin.val_succ] using fin.lt_iff_coe_lt_coe.mp H)
                i.is_le))) :=
  by dsimp [δ, σ]; simpa only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt' CategoryTheory.SimplicialObject.δ_comp_σ_of_gt'

/- warning: category_theory.simplicial_object.σ_comp_σ -> CategoryTheory.SimplicialObject.σ_comp_σ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.σ_comp_σ CategoryTheory.SimplicialObject.σ_comp_σₓ'. -/
/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ i.cast_succ = X.σ i ≫ X.σ j.succ := by dsimp [δ, σ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.simplicial_object.σ_comp_σ CategoryTheory.SimplicialObject.σ_comp_σ

open Simplicial

/- warning: category_theory.simplicial_object.δ_naturality -> CategoryTheory.SimplicialObject.δ_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.δ_naturality CategoryTheory.SimplicialObject.δ_naturalityₓ'. -/
@[simp, reassoc]
theorem δ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (op [n]) = f.app (op [n + 1]) ≫ X'.δ i :=
  f.naturality _
#align category_theory.simplicial_object.δ_naturality CategoryTheory.SimplicialObject.δ_naturality

/- warning: category_theory.simplicial_object.σ_naturality -> CategoryTheory.SimplicialObject.σ_naturality is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.σ_naturality CategoryTheory.SimplicialObject.σ_naturalityₓ'. -/
@[simp, reassoc]
theorem σ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (op [n + 1]) = f.app (op [n]) ≫ X'.σ i :=
  f.naturality _
#align category_theory.simplicial_object.σ_naturality CategoryTheory.SimplicialObject.σ_naturality

variable (C)

#print CategoryTheory.SimplicialObject.whiskering /-
/-- Functor composition induces a functor on simplicial objects. -/
@[simps]
def whiskering (D : Type _) [Category D] : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D :=
  whiskeringRight _ _ _
#align category_theory.simplicial_object.whiskering CategoryTheory.SimplicialObject.whiskering
-/

#print CategoryTheory.SimplicialObject.Truncated /-
/-- Truncated simplicial objects. -/
@[nolint has_nonempty_instance]
def Truncated (n : ℕ) :=
  (SimplexCategory.Truncated n)ᵒᵖ ⥤ C deriving Category
#align category_theory.simplicial_object.truncated CategoryTheory.SimplicialObject.Truncated
-/

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject.Truncated C n) := by dsimp [truncated]; infer_instance

instance {n} [HasLimits C] : HasLimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject.Truncated C n) := by dsimp [truncated]; infer_instance

instance {n} [HasColimits C] : HasColimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

#print CategoryTheory.SimplicialObject.Truncated.whiskering /-
/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps]
def whiskering {n} (D : Type _) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _
#align category_theory.simplicial_object.truncated.whiskering CategoryTheory.SimplicialObject.Truncated.whiskering
-/

variable {C}

end Truncated

section Skeleton

#print CategoryTheory.SimplicialObject.sk /-
/-- The skeleton functor from simplicial objects to truncated simplicial objects. -/
def sk (n : ℕ) : SimplicialObject C ⥤ SimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion.op
#align category_theory.simplicial_object.sk CategoryTheory.SimplicialObject.sk
-/

end Skeleton

variable (C)

#print CategoryTheory.SimplicialObject.const /-
/-- The constant simplicial object is the constant functor. -/
abbrev const : C ⥤ SimplicialObject C :=
  CategoryTheory.Functor.const _
#align category_theory.simplicial_object.const CategoryTheory.SimplicialObject.const
-/

#print CategoryTheory.SimplicialObject.Augmented /-
/-- The category of augmented simplicial objects, defined as a comma category. -/
@[nolint has_nonempty_instance]
def Augmented :=
  Comma (𝟭 (SimplicialObject C)) (const C)deriving Category
#align category_theory.simplicial_object.augmented CategoryTheory.SimplicialObject.Augmented
-/

variable {C}

namespace Augmented

#print CategoryTheory.SimplicialObject.Augmented.drop /-
/-- Drop the augmentation. -/
@[simps]
def drop : Augmented C ⥤ SimplicialObject C :=
  Comma.fst _ _
#align category_theory.simplicial_object.augmented.drop CategoryTheory.SimplicialObject.Augmented.drop
-/

#print CategoryTheory.SimplicialObject.Augmented.point /-
/-- The point of the augmentation. -/
@[simps]
def point : Augmented C ⥤ C :=
  Comma.snd _ _
#align category_theory.simplicial_object.augmented.point CategoryTheory.SimplicialObject.Augmented.point
-/

#print CategoryTheory.SimplicialObject.Augmented.toArrow /-
/-- The functor from augmented objects to arrows. -/
@[simps]
def toArrow : Augmented C ⥤ Arrow C
    where
  obj X :=
    { left := drop.obj X _[0]
      right := point.obj X
      Hom := X.Hom.app _ }
  map X Y η :=
    { left := (drop.map η).app _
      right := point.map η
      w' := by
        dsimp
        rw [← nat_trans.comp_app]
        erw [η.w]
        rfl }
#align category_theory.simplicial_object.augmented.to_arrow CategoryTheory.SimplicialObject.Augmented.toArrow
-/

/- warning: category_theory.simplicial_object.augmented.w₀ -> CategoryTheory.SimplicialObject.Augmented.w₀ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.augmented.w₀ CategoryTheory.SimplicialObject.Augmented.w₀ₓ'. -/
/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    (Augmented.drop.map f).app (op (SimplexCategory.mk 0)) ≫ Y.Hom.app (op (SimplexCategory.mk 0)) =
      X.Hom.app (op (SimplexCategory.mk 0)) ≫ Augmented.point.map f :=
  by convert congr_app f.w (op (SimplexCategory.mk 0))
#align category_theory.simplicial_object.augmented.w₀ CategoryTheory.SimplicialObject.Augmented.w₀

variable (C)

#print CategoryTheory.SimplicialObject.Augmented.whiskeringObj /-
/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskeringObj (D : Type _) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D
    where
  obj X :=
    { left := ((whiskering _ _).obj F).obj (drop.obj X)
      right := F.obj (point.obj X)
      Hom := whiskerRight X.Hom F ≫ (Functor.constComp _ _ _).Hom }
  map X Y η :=
    { left := whiskerRight η.left _
      right := F.map η.right
      w' := by
        ext
        dsimp
        rw [category.comp_id, category.comp_id, ← F.map_comp, ← F.map_comp, ← nat_trans.comp_app]
        erw [η.w]
        rfl }
#align category_theory.simplicial_object.augmented.whiskering_obj CategoryTheory.SimplicialObject.Augmented.whiskeringObj
-/

#print CategoryTheory.SimplicialObject.Augmented.whiskering /-
/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D
    where
  obj := whiskeringObj _ _
  map X Y η :=
    {
      app := fun A =>
        { left := whiskerLeft _ η
          right := η.app _
          w' := by
            ext n
            dsimp
            rw [category.comp_id, category.comp_id, η.naturality] } }
#align category_theory.simplicial_object.augmented.whiskering CategoryTheory.SimplicialObject.Augmented.whiskering
-/

variable {C}

end Augmented

/- warning: category_theory.simplicial_object.augment -> CategoryTheory.SimplicialObject.augment is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.augment CategoryTheory.SimplicialObject.augmentₓ'. -/
/-- Augment a simplicial object with an object. -/
@[simps]
def augment (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀)
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : [0] ⟶ i), X.map g₁.op ≫ f = X.map g₂.op ≫ f) :
    SimplicialObject.Augmented C where
  left := X
  right := X₀
  Hom :=
    { app := fun i => X.map (SimplexCategory.const i.unop 0).op ≫ f
      naturality' := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← category.assoc, category.comp_id, ← op_comp] using w _ _ _ }
#align category_theory.simplicial_object.augment CategoryTheory.SimplicialObject.augment

/- warning: category_theory.simplicial_object.augment_hom_zero -> CategoryTheory.SimplicialObject.augment_hom_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_object.augment_hom_zero CategoryTheory.SimplicialObject.augment_hom_zeroₓ'. -/
@[simp]
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀) (w) :
    (X.augment X₀ f w).Hom.app (op [0]) = f := by dsimp;
  rw [SimplexCategory.hom_zero_zero ([0].const 0), op_id, X.map_id, category.id_comp]
#align category_theory.simplicial_object.augment_hom_zero CategoryTheory.SimplicialObject.augment_hom_zero

end SimplicialObject

#print CategoryTheory.CosimplicialObject /-
/-- Cosimplicial objects. -/
@[nolint has_nonempty_instance]
def CosimplicialObject :=
  SimplexCategory ⥤ C deriving Category
#align category_theory.cosimplicial_object CategoryTheory.CosimplicialObject
-/

namespace CosimplicialObject

-- mathport name: cosimplicial_object.at
scoped[Simplicial]
  notation:1000 X " _[" n "]" =>
    (X : CategoryTheory.CosimplicialObject hole!).obj (SimplexCategory.mk n)

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject C) := by dsimp [cosimplicial_object]; infer_instance

instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject C) := by dsimp [cosimplicial_object]; infer_instance

instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C} (X : CosimplicialObject C)

/- warning: category_theory.cosimplicial_object.δ -> CategoryTheory.CosimplicialObject.δ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ CategoryTheory.CosimplicialObject.δₓ'. -/
/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.δ i)
#align category_theory.cosimplicial_object.δ CategoryTheory.CosimplicialObject.δ

/- warning: category_theory.cosimplicial_object.σ -> CategoryTheory.CosimplicialObject.σ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat}, (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))) -> (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.σ CategoryTheory.CosimplicialObject.σₓ'. -/
/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.σ i)
#align category_theory.cosimplicial_object.σ CategoryTheory.CosimplicialObject.σ

/- warning: category_theory.cosimplicial_object.eq_to_iso -> CategoryTheory.CosimplicialObject.eqToIso is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} {m : Nat}, (Eq.{1} Nat n m) -> (CategoryTheory.Iso.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk m)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} {m : Nat}, (Eq.{1} Nat n m) -> (CategoryTheory.Iso.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk m)))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.eq_to_iso CategoryTheory.CosimplicialObject.eqToIsoₓ'. -/
/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (eqToIso (by rw [h]))
#align category_theory.cosimplicial_object.eq_to_iso CategoryTheory.CosimplicialObject.eqToIso

/- warning: category_theory.cosimplicial_object.eq_to_iso_refl -> CategoryTheory.CosimplicialObject.eqToIso_refl is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} (h : Eq.{1} Nat n n), Eq.{succ u1} (CategoryTheory.Iso.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n))) (CategoryTheory.CosimplicialObject.eqToIso.{u1, u2} C _inst_1 X n n h) (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} (h : Eq.{1} Nat n n), Eq.{succ u1} (CategoryTheory.Iso.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n))) (CategoryTheory.CosimplicialObject.eqToIso.{u1, u2} C _inst_1 X n n h) (CategoryTheory.Iso.refl.{u1, u2} C _inst_1 (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.eq_to_iso_refl CategoryTheory.CosimplicialObject.eqToIso_reflₓ'. -/
@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by ext; simp [eq_to_iso]
#align category_theory.cosimplicial_object.eq_to_iso_refl CategoryTheory.CosimplicialObject.eqToIso_refl

/- warning: category_theory.cosimplicial_object.δ_comp_δ -> CategoryTheory.CosimplicialObject.δ_comp_δ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_δ CategoryTheory.CosimplicialObject.δ_comp_δₓ'. -/
/-- The generic case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ i.cast_succ := by dsimp [δ];
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.cosimplicial_object.δ_comp_δ CategoryTheory.CosimplicialObject.δ_comp_δ

/- warning: category_theory.cosimplicial_object.δ_comp_δ' -> CategoryTheory.CosimplicialObject.δ_comp_δ' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_δ' CategoryTheory.CosimplicialObject.δ_comp_δ'ₓ'. -/
@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.cast_succ < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred fun hj => by simpa only [hj, Fin.not_lt_zero] using H) ≫ X.δ i.cast_succ :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.cosimplicial_object.δ_comp_δ' CategoryTheory.CosimplicialObject.δ_comp_δ'

/- warning: category_theory.cosimplicial_object.δ_comp_δ'' -> CategoryTheory.CosimplicialObject.δ_comp_δ'' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_δ'' CategoryTheory.CosimplicialObject.δ_comp_δ''ₓ'. -/
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ j.cast_succ) :
    X.δ (i.cast_lt (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.cosimplicial_object.δ_comp_δ'' CategoryTheory.CosimplicialObject.δ_comp_δ''

/- warning: category_theory.cosimplicial_object.δ_comp_δ_self -> CategoryTheory.CosimplicialObject.δ_comp_δ_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_δ_self CategoryTheory.CosimplicialObject.δ_comp_δ_selfₓ'. -/
/-- The special case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : X.δ i ≫ X.δ i.cast_succ = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]; simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self CategoryTheory.CosimplicialObject.δ_comp_δ_self

/- warning: category_theory.cosimplicial_object.δ_comp_δ_self' -> CategoryTheory.CosimplicialObject.δ_comp_δ_self' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_δ_self' CategoryTheory.CosimplicialObject.δ_comp_δ_self'ₓ'. -/
@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.cast_succ) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by subst H; rw [δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self' CategoryTheory.CosimplicialObject.δ_comp_δ_self'

/- warning: category_theory.cosimplicial_object.δ_comp_σ_of_le -> CategoryTheory.CosimplicialObject.δ_comp_σ_of_le is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_σ_of_le CategoryTheory.CosimplicialObject.δ_comp_σ_of_leₓ'. -/
/-- The second cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.cast_succ) :
    X.δ i.cast_succ ≫ X.σ j.succ = X.σ j ≫ X.δ i := by dsimp [δ, σ];
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_le CategoryTheory.CosimplicialObject.δ_comp_σ_of_le

/- warning: category_theory.cosimplicial_object.δ_comp_σ_self -> CategoryTheory.CosimplicialObject.δ_comp_σ_self is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_σ_self CategoryTheory.CosimplicialObject.δ_comp_σ_selfₓ'. -/
/-- The first part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ i.cast_succ ≫ X.σ i = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_self CategoryTheory.CosimplicialObject.δ_comp_σ_self

/- warning: category_theory.cosimplicial_object.δ_comp_σ_self' -> CategoryTheory.CosimplicialObject.δ_comp_σ_self' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_σ_self' CategoryTheory.CosimplicialObject.δ_comp_σ_self'ₓ'. -/
@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.cast_succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by subst H; rw [δ_comp_σ_self]
#align category_theory.cosimplicial_object.δ_comp_σ_self' CategoryTheory.CosimplicialObject.δ_comp_σ_self'

/- warning: category_theory.cosimplicial_object.δ_comp_σ_succ -> CategoryTheory.CosimplicialObject.δ_comp_σ_succ is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X n (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i)) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X n i)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))}, Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X n (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i)) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X n i)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_σ_succ CategoryTheory.CosimplicialObject.δ_comp_σ_succₓ'. -/
/-- The second part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_succ CategoryTheory.CosimplicialObject.δ_comp_σ_succ

/- warning: category_theory.cosimplicial_object.δ_comp_σ_succ' -> CategoryTheory.CosimplicialObject.δ_comp_σ_succ' is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} {j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))}, (Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))) j (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))) i)) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X n j) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X n i)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n))))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) {n : Nat} {j : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))} {i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))}, (Eq.{1} (Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))) j (Fin.succ (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))) i)) -> (Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X n j) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X n i)) (CategoryTheory.CategoryStruct.id.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n))))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_σ_succ' CategoryTheory.CosimplicialObject.δ_comp_σ_succ'ₓ'. -/
@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by subst H; rw [δ_comp_σ_succ]
#align category_theory.cosimplicial_object.δ_comp_σ_succ' CategoryTheory.CosimplicialObject.δ_comp_σ_succ'

/- warning: category_theory.cosimplicial_object.δ_comp_σ_of_gt -> CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_σ_of_gt CategoryTheory.CosimplicialObject.δ_comp_σ_of_gtₓ'. -/
/-- The fourth cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.cast_succ < i) :
    X.δ i.succ ≫ X.σ j.cast_succ = X.σ j ≫ X.δ i := by dsimp [δ, σ];
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt

/- warning: category_theory.cosimplicial_object.δ_comp_σ_of_gt' -> CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_comp_σ_of_gt' CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt'ₓ'. -/
@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ
          (j.cast_lt
            ((add_lt_add_iff_right 1).mp
              (lt_of_lt_of_le
                (by simpa only [[anonymous], ← Fin.val_succ] using fin.lt_iff_coe_lt_coe.mp H)
                i.is_le))) ≫
        X.δ (i.pred fun hi => by simpa only [Fin.not_lt_zero, hi] using H) :=
  by dsimp [δ, σ]; simpa only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt' CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt'

/- warning: category_theory.cosimplicial_object.σ_comp_σ -> CategoryTheory.CosimplicialObject.σ_comp_σ is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.σ_comp_σ CategoryTheory.CosimplicialObject.σ_comp_σₓ'. -/
/-- The fifth cosimplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ i.cast_succ ≫ X.σ j = X.σ j.succ ≫ X.σ i := by dsimp [δ, σ];
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.cosimplicial_object.σ_comp_σ CategoryTheory.CosimplicialObject.σ_comp_σ

/- warning: category_theory.cosimplicial_object.δ_naturality -> CategoryTheory.CosimplicialObject.δ_naturality is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X' : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} {X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u1 u2} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u2} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u2} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.CosimplicialObject.category.{u1, u2} C _inst_1))) X X') {n : Nat} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 2 (OfNat.mk.{0} Nat 2 (bit0.{0} Nat Nat.hasAdd (One.one.{0} Nat Nat.hasOne)))))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X n i) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X' n i))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X' : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} {X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u2 u1} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.instCategoryCosimplicialObject.{u1, u2} C _inst_1))) X X') {n : Nat} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 2 (instOfNatNat 2)))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X n i) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.δ.{u1, u2} C _inst_1 X' n i))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.δ_naturality CategoryTheory.CosimplicialObject.δ_naturalityₓ'. -/
@[simp, reassoc]
theorem δ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (SimplexCategory.mk (n + 1)) = f.app (SimplexCategory.mk n) ≫ X'.δ i :=
  f.naturality _
#align category_theory.cosimplicial_object.δ_naturality CategoryTheory.CosimplicialObject.δ_naturality

/- warning: category_theory.cosimplicial_object.σ_naturality -> CategoryTheory.CosimplicialObject.σ_naturality is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X' : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} {X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u1 u2} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u1 u2} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u1 u2} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.CosimplicialObject.category.{u1, u2} C _inst_1))) X X') {n : Nat} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne))))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk n)) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X n i) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X' (SimplexCategory.mk n)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat Nat.hasAdd) n (OfNat.ofNat.{0} Nat 1 (OfNat.mk.{0} Nat 1 (One.one.{0} Nat Nat.hasOne)))))) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X' n i))
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] {X' : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} {X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1} (f : Quiver.Hom.{succ u1, max u2 u1} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.CategoryStruct.toQuiver.{u1, max u2 u1} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.Category.toCategoryStruct.{u1, max u2 u1} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.instCategoryCosimplicialObject.{u1, u2} C _inst_1))) X X') {n : Nat} (i : Fin (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1)))), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk n)) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk n)) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X n i) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk n))) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X') (SimplexCategory.mk n)) (CategoryTheory.NatTrans.app.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X X' f (SimplexCategory.mk (HAdd.hAdd.{0, 0, 0} Nat Nat Nat (instHAdd.{0} Nat instAddNat) n (OfNat.ofNat.{0} Nat 1 (instOfNatNat 1))))) (CategoryTheory.CosimplicialObject.σ.{u1, u2} C _inst_1 X' n i))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.σ_naturality CategoryTheory.CosimplicialObject.σ_naturalityₓ'. -/
@[simp, reassoc]
theorem σ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (SimplexCategory.mk n) = f.app (SimplexCategory.mk (n + 1)) ≫ X'.σ i :=
  f.naturality _
#align category_theory.cosimplicial_object.σ_naturality CategoryTheory.CosimplicialObject.σ_naturality

variable (C)

#print CategoryTheory.CosimplicialObject.whiskering /-
/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps]
def whiskering (D : Type _) [Category D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ CosimplicialObject D :=
  whiskeringRight _ _ _
#align category_theory.cosimplicial_object.whiskering CategoryTheory.CosimplicialObject.whiskering
-/

#print CategoryTheory.CosimplicialObject.Truncated /-
/-- Truncated cosimplicial objects. -/
@[nolint has_nonempty_instance]
def Truncated (n : ℕ) :=
  SimplexCategory.Truncated n ⥤ C deriving Category
#align category_theory.cosimplicial_object.truncated CategoryTheory.CosimplicialObject.Truncated
-/

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by dsimp [truncated]; infer_instance

instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by dsimp [truncated]; infer_instance

instance {n} [HasColimits C] : HasColimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

#print CategoryTheory.CosimplicialObject.Truncated.whiskering /-
/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps]
def whiskering {n} (D : Type _) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _
#align category_theory.cosimplicial_object.truncated.whiskering CategoryTheory.CosimplicialObject.Truncated.whiskering
-/

variable {C}

end Truncated

section Skeleton

#print CategoryTheory.CosimplicialObject.sk /-
/-- The skeleton functor from cosimplicial objects to truncated cosimplicial objects. -/
def sk (n : ℕ) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion
#align category_theory.cosimplicial_object.sk CategoryTheory.CosimplicialObject.sk
-/

end Skeleton

variable (C)

#print CategoryTheory.CosimplicialObject.const /-
/-- The constant cosimplicial object. -/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _
#align category_theory.cosimplicial_object.const CategoryTheory.CosimplicialObject.const
-/

#print CategoryTheory.CosimplicialObject.Augmented /-
/-- Augmented cosimplicial objects. -/
@[nolint has_nonempty_instance]
def Augmented :=
  Comma (const C) (𝟭 (CosimplicialObject C))deriving Category
#align category_theory.cosimplicial_object.augmented CategoryTheory.CosimplicialObject.Augmented
-/

variable {C}

namespace Augmented

#print CategoryTheory.CosimplicialObject.Augmented.drop /-
/-- Drop the augmentation. -/
@[simps]
def drop : Augmented C ⥤ CosimplicialObject C :=
  Comma.snd _ _
#align category_theory.cosimplicial_object.augmented.drop CategoryTheory.CosimplicialObject.Augmented.drop
-/

#print CategoryTheory.CosimplicialObject.Augmented.point /-
/-- The point of the augmentation. -/
@[simps]
def point : Augmented C ⥤ C :=
  Comma.fst _ _
#align category_theory.cosimplicial_object.augmented.point CategoryTheory.CosimplicialObject.Augmented.point
-/

#print CategoryTheory.CosimplicialObject.Augmented.toArrow /-
/-- The functor from augmented objects to arrows. -/
@[simps]
def toArrow : Augmented C ⥤ Arrow C
    where
  obj X :=
    { left := point.obj X
      right := drop.obj X _[0]
      Hom := X.Hom.app _ }
  map X Y η :=
    { left := point.map η
      right := (drop.map η).app _
      w' := by
        dsimp
        rw [← nat_trans.comp_app]
        erw [← η.w]
        rfl }
#align category_theory.cosimplicial_object.augmented.to_arrow CategoryTheory.CosimplicialObject.Augmented.toArrow
-/

variable (C)

#print CategoryTheory.CosimplicialObject.Augmented.whiskeringObj /-
/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
def whiskeringObj (D : Type _) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D
    where
  obj X :=
    { left := F.obj (point.obj X)
      right := ((whiskering _ _).obj F).obj (drop.obj X)
      Hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.Hom F }
  map X Y η :=
    { left := F.map η.left
      right := whiskerRight η.right _
      w' := by
        ext
        dsimp
        rw [category.id_comp, category.id_comp, ← F.map_comp, ← F.map_comp, ← nat_trans.comp_app]
        erw [← η.w]
        rfl }
#align category_theory.cosimplicial_object.augmented.whiskering_obj CategoryTheory.CosimplicialObject.Augmented.whiskeringObj
-/

#print CategoryTheory.CosimplicialObject.Augmented.whiskering /-
/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D
    where
  obj := whiskeringObj _ _
  map X Y η :=
    {
      app := fun A =>
        { left := η.app _
          right := whiskerLeft _ η
          w' := by
            ext n
            dsimp
            rw [category.id_comp, category.id_comp, η.naturality] } }
#align category_theory.cosimplicial_object.augmented.whiskering CategoryTheory.CosimplicialObject.Augmented.whiskering
-/

variable {C}

end Augmented

open Simplicial

/- warning: category_theory.cosimplicial_object.augment -> CategoryTheory.CosimplicialObject.augment is a dubious translation:
lean 3 declaration is
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (X₀ : C) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X₀ (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))))), (forall (i : SimplexCategory) (g₁ : Quiver.Hom.{1, 0} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) i) (g₂ : Quiver.Hom.{1, 0} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) i), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X₀ (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X i)) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X₀ (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X i) f (CategoryTheory.Functor.map.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) i g₁)) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X₀ (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero))))) (CategoryTheory.Functor.obj.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X i) f (CategoryTheory.Functor.map.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (OfNat.mk.{0} Nat 0 (Zero.zero.{0} Nat Nat.hasZero)))) i g₂))) -> (CategoryTheory.CosimplicialObject.Augmented.{u1, u2} C _inst_1)
but is expected to have type
  forall {C : Type.{u2}} [_inst_1 : CategoryTheory.Category.{u1, u2} C] (X : CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (X₀ : C) (f : Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X₀ (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))))), (forall (i : SimplexCategory) (g₁ : Quiver.Hom.{1, 0} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) i) (g₂ : Quiver.Hom.{1, 0} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) i), Eq.{succ u1} (Quiver.Hom.{succ u1, u2} C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) X₀ (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) i)) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X₀ (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) i) f (Prefunctor.map.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) i g₁)) (CategoryTheory.CategoryStruct.comp.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1) X₀ (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0)))) (Prefunctor.obj.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) i) f (Prefunctor.map.{1, succ u1, 0, u2} SimplexCategory (CategoryTheory.CategoryStruct.toQuiver.{0, 0} SimplexCategory (CategoryTheory.Category.toCategoryStruct.{0, 0} SimplexCategory SimplexCategory.smallCategory)) C (CategoryTheory.CategoryStruct.toQuiver.{u1, u2} C (CategoryTheory.Category.toCategoryStruct.{u1, u2} C _inst_1)) (CategoryTheory.Functor.toPrefunctor.{0, u1, 0, u2} SimplexCategory SimplexCategory.smallCategory C _inst_1 X) (SimplexCategory.mk (OfNat.ofNat.{0} Nat 0 (instOfNatNat 0))) i g₂))) -> (CategoryTheory.CosimplicialObject.Augmented.{u1, u2} C _inst_1)
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.augment CategoryTheory.CosimplicialObject.augmentₓ'. -/
/-- Augment a cosimplicial object with an object. -/
@[simps]
def augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0])
    (w : ∀ (i : SimplexCategory) (g₁ g₂ : [0] ⟶ i), f ≫ X.map g₁ = f ≫ X.map g₂) :
    CosimplicialObject.Augmented C where
  left := X₀
  right := X
  Hom :=
    { app := fun i => f ≫ X.map (SimplexCategory.const i 0)
      naturality' := by
        intro i j g
        dsimp
        simpa [← X.map_comp] using w _ _ _ }
#align category_theory.cosimplicial_object.augment CategoryTheory.CosimplicialObject.augment

/- warning: category_theory.cosimplicial_object.augment_hom_zero -> CategoryTheory.CosimplicialObject.augment_hom_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_object.augment_hom_zero CategoryTheory.CosimplicialObject.augment_hom_zeroₓ'. -/
@[simp]
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) (w) :
    (X.augment X₀ f w).Hom.app [0] = f := by dsimp;
  rw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, category.comp_id]
#align category_theory.cosimplicial_object.augment_hom_zero CategoryTheory.CosimplicialObject.augment_hom_zero

end CosimplicialObject

/- warning: category_theory.simplicial_cosimplicial_equiv -> CategoryTheory.simplicialCosimplicialEquiv is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, max u1 u2, max u1 u2} (Opposite.{succ (max u1 u2)} (CategoryTheory.SimplicialObject.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u1 u2} (CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.SimplicialObject.category.{u1, u2} C _inst_1)) (CategoryTheory.CosimplicialObject.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.CosimplicialObject.category.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, max u2 u1, max u2 u1} (Opposite.{max (succ u2) (succ u1)} (CategoryTheory.SimplicialObject.{u1, u2} C _inst_1)) (CategoryTheory.CosimplicialObject.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 u1} (CategoryTheory.SimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.instCategorySimplicialObject.{u1, u2} C _inst_1)) (CategoryTheory.instCategoryCosimplicialObject.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_cosimplicial_equiv CategoryTheory.simplicialCosimplicialEquivₓ'. -/
/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps]
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _
#align category_theory.simplicial_cosimplicial_equiv CategoryTheory.simplicialCosimplicialEquiv

/- warning: category_theory.cosimplicial_simplicial_equiv -> CategoryTheory.cosimplicialSimplicialEquiv is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, max u1 u2, max u1 u2} (Opposite.{succ (max u1 u2)} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u1 u2} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.CosimplicialObject.category.{u1, u2} C _inst_1)) (CategoryTheory.SimplicialObject.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.SimplicialObject.category.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, max u2 u1, max u2 u1} (Opposite.{max (succ u2) (succ u1)} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1)) (CategoryTheory.SimplicialObject.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 u1} (CategoryTheory.CosimplicialObject.{u1, u2} C _inst_1) (CategoryTheory.instCategoryCosimplicialObject.{u1, u2} C _inst_1)) (CategoryTheory.instCategorySimplicialObject.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.cosimplicial_simplicial_equiv CategoryTheory.cosimplicialSimplicialEquivₓ'. -/
/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps]
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _
#align category_theory.cosimplicial_simplicial_equiv CategoryTheory.cosimplicialSimplicialEquiv

variable {C}

#print CategoryTheory.SimplicialObject.Augmented.rightOp /-
/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps]
def SimplicialObject.Augmented.rightOp (X : SimplicialObject.Augmented C) :
    CosimplicialObject.Augmented Cᵒᵖ
    where
  left := Opposite.op X.right
  right := X.left.rightOp
  Hom := X.Hom.rightOp
#align category_theory.simplicial_object.augmented.right_op CategoryTheory.SimplicialObject.Augmented.rightOp
-/

#print CategoryTheory.CosimplicialObject.Augmented.leftOp /-
/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps]
def CosimplicialObject.Augmented.leftOp (X : CosimplicialObject.Augmented Cᵒᵖ) :
    SimplicialObject.Augmented C where
  left := X.right.leftOp
  right := X.left.unop
  Hom := X.Hom.leftOp
#align category_theory.cosimplicial_object.augmented.left_op CategoryTheory.CosimplicialObject.Augmented.leftOp
-/

#print CategoryTheory.SimplicialObject.Augmented.rightOpLeftOpIso /-
/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps]
def SimplicialObject.Augmented.rightOpLeftOpIso (X : SimplicialObject.Augmented C) :
    X.rightOp.leftOp ≅ X :=
  Comma.isoMk X.left.rightOpLeftOpIso (eqToIso <| by simp) (by tidy)
#align category_theory.simplicial_object.augmented.right_op_left_op_iso CategoryTheory.SimplicialObject.Augmented.rightOpLeftOpIso
-/

#print CategoryTheory.CosimplicialObject.Augmented.leftOpRightOpIso /-
/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps]
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) :
    X.leftOp.rightOp ≅ X :=
  Comma.isoMk (eqToIso <| by simp) X.right.leftOpRightOpIso (by tidy)
#align category_theory.cosimplicial_object.augmented.left_op_right_op_iso CategoryTheory.CosimplicialObject.Augmented.leftOpRightOpIso
-/

variable (C)

#print CategoryTheory.simplicialToCosimplicialAugmented /-
/-- A functorial version of `simplicial_object.augmented.right_op`. -/
@[simps]
def simplicialToCosimplicialAugmented :
    (SimplicialObject.Augmented C)ᵒᵖ ⥤ CosimplicialObject.Augmented Cᵒᵖ
    where
  obj X := X.unop.rightOp
  map X Y f :=
    { left := f.unop.right.op
      right := f.unop.left.rightOp
      w' := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }
#align category_theory.simplicial_to_cosimplicial_augmented CategoryTheory.simplicialToCosimplicialAugmented
-/

#print CategoryTheory.cosimplicialToSimplicialAugmented /-
/-- A functorial version of `cosimplicial_object.augmented.left_op`. -/
@[simps]
def cosimplicialToSimplicialAugmented :
    CosimplicialObject.Augmented Cᵒᵖ ⥤ (SimplicialObject.Augmented C)ᵒᵖ
    where
  obj X := Opposite.op X.leftOp
  map X Y f :=
    Quiver.Hom.op <|
      { left := f.right.leftOp
        right := f.left.unop
        w' := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w x.unop).symm }
#align category_theory.cosimplicial_to_simplicial_augmented CategoryTheory.cosimplicialToSimplicialAugmented
-/

/- warning: category_theory.simplicial_cosimplicial_augmented_equiv -> CategoryTheory.simplicialCosimplicialAugmentedEquiv is a dubious translation:
lean 3 declaration is
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, max (max u1 u2) u2 u1, max u1 u2} (Opposite.{succ (max (max u1 u2) u2 u1)} (CategoryTheory.SimplicialObject.Augmented.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max (max u1 u2) u2 u1} (CategoryTheory.SimplicialObject.Augmented.{u1, u2} C _inst_1) (CategoryTheory.SimplicialObject.Augmented.category.{u1, u2} C _inst_1)) (CategoryTheory.CosimplicialObject.Augmented.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.CosimplicialObject.Augmented.category.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))
but is expected to have type
  forall (C : Type.{u2}) [_inst_1 : CategoryTheory.Category.{u1, u2} C], CategoryTheory.Equivalence.{u1, u1, max u2 u1, max u2 u1} (Opposite.{max (succ u2) (succ u1)} (CategoryTheory.SimplicialObject.Augmented.{u1, u2} C _inst_1)) (CategoryTheory.CosimplicialObject.Augmented.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1)) (CategoryTheory.Category.opposite.{u1, max u2 u1} (CategoryTheory.SimplicialObject.Augmented.{u1, u2} C _inst_1) (CategoryTheory.SimplicialObject.instCategoryAugmented.{u1, u2} C _inst_1)) (CategoryTheory.CosimplicialObject.instCategoryAugmented.{u1, u2} (Opposite.{succ u2} C) (CategoryTheory.Category.opposite.{u1, u2} C _inst_1))
Case conversion may be inaccurate. Consider using '#align category_theory.simplicial_cosimplicial_augmented_equiv CategoryTheory.simplicialCosimplicialAugmentedEquivₓ'. -/
/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps Functor inverse]
def simplicialCosimplicialAugmentedEquiv :
    (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ :=
  Equivalence.mk (simplicialToCosimplicialAugmented _) (cosimplicialToSimplicialAugmented _)
    (NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op) fun X Y f => by dsimp;
      rw [← f.op_unop]; simp_rw [← op_comp]; congr 1; tidy)
    ((NatIso.ofComponents fun X => X.leftOpRightOpIso) <| by tidy)
#align category_theory.simplicial_cosimplicial_augmented_equiv CategoryTheory.simplicialCosimplicialAugmentedEquiv

end CategoryTheory

