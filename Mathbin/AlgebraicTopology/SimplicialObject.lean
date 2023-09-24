/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import AlgebraicTopology.SimplexCategory
import CategoryTheory.Arrow
import CategoryTheory.Limits.FunctorCategory
import CategoryTheory.Opposites

#align_import algebraic_topology.simplicial_object from "leanprover-community/mathlib"@"814d76e2247d5ba8bc024843552da1278bfe9e5c"

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
  SimplexCategoryᵒᵖ ⥤ C
deriving Category
#align category_theory.simplicial_object CategoryTheory.SimplicialObject
-/

namespace SimplicialObject

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

#print CategoryTheory.SimplicialObject.δ /-
/-- Face maps for a simplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.δ i).op
#align category_theory.simplicial_object.δ CategoryTheory.SimplicialObject.δ
-/

#print CategoryTheory.SimplicialObject.σ /-
/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.σ i).op
#align category_theory.simplicial_object.σ CategoryTheory.SimplicialObject.σ
-/

#print CategoryTheory.SimplicialObject.eqToIso /-
/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (eqToIso (by rw [h]))
#align category_theory.simplicial_object.eq_to_iso CategoryTheory.SimplicialObject.eqToIso
-/

#print CategoryTheory.SimplicialObject.eqToIso_refl /-
@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by ext; simp [eq_to_iso]
#align category_theory.simplicial_object.eq_to_iso_refl CategoryTheory.SimplicialObject.eqToIso_refl
-/

#print CategoryTheory.SimplicialObject.δ_comp_δ /-
/-- The generic case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j := by dsimp [δ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.simplicial_object.δ_comp_δ CategoryTheory.SimplicialObject.δ_comp_δ
-/

#print CategoryTheory.SimplicialObject.δ_comp_δ' /-
@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.cast_succ < j) :
    X.δ j ≫ X.δ i =
      X.δ i.cast_succ ≫ X.δ (j.pred fun hj => by simpa only [hj, Fin.not_lt_zero] using H) :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.simplicial_object.δ_comp_δ' CategoryTheory.SimplicialObject.δ_comp_δ'
-/

#print CategoryTheory.SimplicialObject.δ_comp_δ'' /-
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ j.cast_succ) :
    X.δ j.succ ≫ X.δ (i.cast_lt (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) =
      X.δ i ≫ X.δ j :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.simplicial_object.δ_comp_δ'' CategoryTheory.SimplicialObject.δ_comp_δ''
-/

#print CategoryTheory.SimplicialObject.δ_comp_δ_self /-
/-- The special case of the first simplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : X.δ i.cast_succ ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self CategoryTheory.SimplicialObject.δ_comp_δ_self
-/

#print CategoryTheory.SimplicialObject.δ_comp_δ_self' /-
@[reassoc]
theorem δ_comp_δ_self' {n} {j : Fin (n + 3)} {i : Fin (n + 2)} (H : j = i.cast_succ) :
    X.δ j ≫ X.δ i = X.δ i.succ ≫ X.δ i := by subst H; rw [δ_comp_δ_self]
#align category_theory.simplicial_object.δ_comp_δ_self' CategoryTheory.SimplicialObject.δ_comp_δ_self'
-/

#print CategoryTheory.SimplicialObject.δ_comp_σ_of_le /-
/-- The second simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.cast_succ) :
    X.σ j.succ ≫ X.δ i.cast_succ = X.δ i ≫ X.σ j := by dsimp [δ, σ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.simplicial_object.δ_comp_σ_of_le CategoryTheory.SimplicialObject.δ_comp_σ_of_le
-/

#print CategoryTheory.SimplicialObject.δ_comp_σ_self /-
/-- The first part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.cast_succ = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_self CategoryTheory.SimplicialObject.δ_comp_σ_self
-/

#print CategoryTheory.SimplicialObject.δ_comp_σ_self' /-
@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.cast_succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by subst H; rw [δ_comp_σ_self]
#align category_theory.simplicial_object.δ_comp_σ_self' CategoryTheory.SimplicialObject.δ_comp_σ_self'
-/

#print CategoryTheory.SimplicialObject.δ_comp_σ_succ /-
/-- The second part of the third simplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]
#align category_theory.simplicial_object.δ_comp_σ_succ CategoryTheory.SimplicialObject.δ_comp_σ_succ
-/

#print CategoryTheory.SimplicialObject.δ_comp_σ_succ' /-
@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.σ i ≫ X.δ j = 𝟙 _ := by subst H; rw [δ_comp_σ_succ]
#align category_theory.simplicial_object.δ_comp_σ_succ' CategoryTheory.SimplicialObject.δ_comp_σ_succ'
-/

#print CategoryTheory.SimplicialObject.δ_comp_σ_of_gt /-
/-- The fourth simplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.cast_succ < i) :
    X.σ j.cast_succ ≫ X.δ i.succ = X.δ i ≫ X.σ j := by dsimp [δ, σ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt CategoryTheory.SimplicialObject.δ_comp_σ_of_gt
-/

#print CategoryTheory.SimplicialObject.δ_comp_σ_of_gt' /-
@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.σ j ≫ X.δ i =
      X.δ (i.pred fun hi => by simpa only [Fin.not_lt_zero, hi] using H) ≫
        X.σ
          (j.cast_lt
            ((add_lt_add_iff_right 1).mp
              (lt_of_lt_of_le
                (by simpa only [Fin.val_eq_coe, ← Fin.val_succ] using fin.lt_iff_coe_lt_coe.mp H)
                i.is_le))) :=
  by dsimp [δ, σ]; simpa only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.simplicial_object.δ_comp_σ_of_gt' CategoryTheory.SimplicialObject.δ_comp_σ_of_gt'
-/

#print CategoryTheory.SimplicialObject.σ_comp_σ /-
/-- The fifth simplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ j ≫ X.σ i.cast_succ = X.σ i ≫ X.σ j.succ := by dsimp [δ, σ];
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.simplicial_object.σ_comp_σ CategoryTheory.SimplicialObject.σ_comp_σ
-/

open scoped Simplicial

#print CategoryTheory.SimplicialObject.δ_naturality /-
@[simp, reassoc]
theorem δ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (op [n]) = f.app (op [n + 1]) ≫ X'.δ i :=
  f.naturality _
#align category_theory.simplicial_object.δ_naturality CategoryTheory.SimplicialObject.δ_naturality
-/

#print CategoryTheory.SimplicialObject.σ_naturality /-
@[simp, reassoc]
theorem σ_naturality {X' X : SimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (op [n + 1]) = f.app (op [n]) ≫ X'.σ i :=
  f.naturality _
#align category_theory.simplicial_object.σ_naturality CategoryTheory.SimplicialObject.σ_naturality
-/

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
  (SimplexCategory.Truncated n)ᵒᵖ ⥤ C
deriving Category
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
  Comma (𝟭 (SimplicialObject C)) (const C)
deriving Category
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

#print CategoryTheory.SimplicialObject.Augmented.w₀ /-
/-- The compatibility of a morphism with the augmentation, on 0-simplices -/
@[reassoc]
theorem w₀ {X Y : Augmented C} (f : X ⟶ Y) :
    (Augmented.drop.map f).app (op (SimplexCategory.mk 0)) ≫ Y.Hom.app (op (SimplexCategory.mk 0)) =
      X.Hom.app (op (SimplexCategory.mk 0)) ≫ Augmented.point.map f :=
  by convert congr_app f.w (op (SimplexCategory.mk 0))
#align category_theory.simplicial_object.augmented.w₀ CategoryTheory.SimplicialObject.Augmented.w₀
-/

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

#print CategoryTheory.SimplicialObject.augment /-
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
-/

#print CategoryTheory.SimplicialObject.augment_hom_zero /-
@[simp]
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀) (w) :
    (X.augment X₀ f w).Hom.app (op [0]) = f := by dsimp;
  rw [SimplexCategory.hom_zero_zero ([0].const 0), op_id, X.map_id, category.id_comp]
#align category_theory.simplicial_object.augment_hom_zero CategoryTheory.SimplicialObject.augment_hom_zero
-/

end SimplicialObject

#print CategoryTheory.CosimplicialObject /-
/-- Cosimplicial objects. -/
@[nolint has_nonempty_instance]
def CosimplicialObject :=
  SimplexCategory ⥤ C
deriving Category
#align category_theory.cosimplicial_object CategoryTheory.CosimplicialObject
-/

namespace CosimplicialObject

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

#print CategoryTheory.CosimplicialObject.δ /-
/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : Fin (n + 2)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.δ i)
#align category_theory.cosimplicial_object.δ CategoryTheory.CosimplicialObject.δ
-/

#print CategoryTheory.CosimplicialObject.σ /-
/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : Fin (n + 1)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.σ i)
#align category_theory.cosimplicial_object.σ CategoryTheory.CosimplicialObject.σ
-/

#print CategoryTheory.CosimplicialObject.eqToIso /-
/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso (eqToIso (by rw [h]))
#align category_theory.cosimplicial_object.eq_to_iso CategoryTheory.CosimplicialObject.eqToIso
-/

#print CategoryTheory.CosimplicialObject.eqToIso_refl /-
@[simp]
theorem eqToIso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by ext; simp [eq_to_iso]
#align category_theory.cosimplicial_object.eq_to_iso_refl CategoryTheory.CosimplicialObject.eqToIso_refl
-/

#print CategoryTheory.CosimplicialObject.δ_comp_δ /-
/-- The generic case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ {n} {i j : Fin (n + 2)} (H : i ≤ j) :
    X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ i.cast_succ := by dsimp [δ];
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]
#align category_theory.cosimplicial_object.δ_comp_δ CategoryTheory.CosimplicialObject.δ_comp_δ
-/

#print CategoryTheory.CosimplicialObject.δ_comp_δ' /-
@[reassoc]
theorem δ_comp_δ' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : i.cast_succ < j) :
    X.δ i ≫ X.δ j =
      X.δ (j.pred fun hj => by simpa only [hj, Fin.not_lt_zero] using H) ≫ X.δ i.cast_succ :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ' H]
#align category_theory.cosimplicial_object.δ_comp_δ' CategoryTheory.CosimplicialObject.δ_comp_δ'
-/

#print CategoryTheory.CosimplicialObject.δ_comp_δ'' /-
@[reassoc]
theorem δ_comp_δ'' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : i ≤ j.cast_succ) :
    X.δ (i.cast_lt (Nat.lt_of_le_of_lt (Fin.le_iff_val_le_val.mp H) j.is_lt)) ≫ X.δ j.succ =
      X.δ j ≫ X.δ i :=
  by dsimp [δ]; simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ'' H]
#align category_theory.cosimplicial_object.δ_comp_δ'' CategoryTheory.CosimplicialObject.δ_comp_δ''
-/

#print CategoryTheory.CosimplicialObject.δ_comp_δ_self /-
/-- The special case of the first cosimplicial identity -/
@[reassoc]
theorem δ_comp_δ_self {n} {i : Fin (n + 2)} : X.δ i ≫ X.δ i.cast_succ = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]; simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self CategoryTheory.CosimplicialObject.δ_comp_δ_self
-/

#print CategoryTheory.CosimplicialObject.δ_comp_δ_self' /-
@[reassoc]
theorem δ_comp_δ_self' {n} {i : Fin (n + 2)} {j : Fin (n + 3)} (H : j = i.cast_succ) :
    X.δ i ≫ X.δ j = X.δ i ≫ X.δ i.succ := by subst H; rw [δ_comp_δ_self]
#align category_theory.cosimplicial_object.δ_comp_δ_self' CategoryTheory.CosimplicialObject.δ_comp_δ_self'
-/

#print CategoryTheory.CosimplicialObject.δ_comp_σ_of_le /-
/-- The second cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_le {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : i ≤ j.cast_succ) :
    X.δ i.cast_succ ≫ X.σ j.succ = X.σ j ≫ X.δ i := by dsimp [δ, σ];
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_le CategoryTheory.CosimplicialObject.δ_comp_σ_of_le
-/

#print CategoryTheory.CosimplicialObject.δ_comp_σ_self /-
/-- The first part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_self {n} {i : Fin (n + 1)} : X.δ i.cast_succ ≫ X.σ i = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_self CategoryTheory.CosimplicialObject.δ_comp_σ_self
-/

#print CategoryTheory.CosimplicialObject.δ_comp_σ_self' /-
@[reassoc]
theorem δ_comp_σ_self' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.cast_succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by subst H; rw [δ_comp_σ_self]
#align category_theory.cosimplicial_object.δ_comp_σ_self' CategoryTheory.CosimplicialObject.δ_comp_σ_self'
-/

#print CategoryTheory.CosimplicialObject.δ_comp_σ_succ /-
/-- The second part of the third cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_succ {n} {i : Fin (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ :=
  by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]
#align category_theory.cosimplicial_object.δ_comp_σ_succ CategoryTheory.CosimplicialObject.δ_comp_σ_succ
-/

#print CategoryTheory.CosimplicialObject.δ_comp_σ_succ' /-
@[reassoc]
theorem δ_comp_σ_succ' {n} {j : Fin (n + 2)} {i : Fin (n + 1)} (H : j = i.succ) :
    X.δ j ≫ X.σ i = 𝟙 _ := by subst H; rw [δ_comp_σ_succ]
#align category_theory.cosimplicial_object.δ_comp_σ_succ' CategoryTheory.CosimplicialObject.δ_comp_σ_succ'
-/

#print CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt /-
/-- The fourth cosimplicial identity -/
@[reassoc]
theorem δ_comp_σ_of_gt {n} {i : Fin (n + 2)} {j : Fin (n + 1)} (H : j.cast_succ < i) :
    X.δ i.succ ≫ X.σ j.cast_succ = X.σ j ≫ X.δ i := by dsimp [δ, σ];
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt
-/

#print CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt' /-
@[reassoc]
theorem δ_comp_σ_of_gt' {n} {i : Fin (n + 3)} {j : Fin (n + 2)} (H : j.succ < i) :
    X.δ i ≫ X.σ j =
      X.σ
          (j.cast_lt
            ((add_lt_add_iff_right 1).mp
              (lt_of_lt_of_le
                (by simpa only [Fin.val_eq_coe, ← Fin.val_succ] using fin.lt_iff_coe_lt_coe.mp H)
                i.is_le))) ≫
        X.δ (i.pred fun hi => by simpa only [Fin.not_lt_zero, hi] using H) :=
  by dsimp [δ, σ]; simpa only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt' H]
#align category_theory.cosimplicial_object.δ_comp_σ_of_gt' CategoryTheory.CosimplicialObject.δ_comp_σ_of_gt'
-/

#print CategoryTheory.CosimplicialObject.σ_comp_σ /-
/-- The fifth cosimplicial identity -/
@[reassoc]
theorem σ_comp_σ {n} {i j : Fin (n + 1)} (H : i ≤ j) :
    X.σ i.cast_succ ≫ X.σ j = X.σ j.succ ≫ X.σ i := by dsimp [δ, σ];
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]
#align category_theory.cosimplicial_object.σ_comp_σ CategoryTheory.CosimplicialObject.σ_comp_σ
-/

#print CategoryTheory.CosimplicialObject.δ_naturality /-
@[simp, reassoc]
theorem δ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 2)) :
    X.δ i ≫ f.app (SimplexCategory.mk (n + 1)) = f.app (SimplexCategory.mk n) ≫ X'.δ i :=
  f.naturality _
#align category_theory.cosimplicial_object.δ_naturality CategoryTheory.CosimplicialObject.δ_naturality
-/

#print CategoryTheory.CosimplicialObject.σ_naturality /-
@[simp, reassoc]
theorem σ_naturality {X' X : CosimplicialObject C} (f : X ⟶ X') {n : ℕ} (i : Fin (n + 1)) :
    X.σ i ≫ f.app (SimplexCategory.mk n) = f.app (SimplexCategory.mk (n + 1)) ≫ X'.σ i :=
  f.naturality _
#align category_theory.cosimplicial_object.σ_naturality CategoryTheory.CosimplicialObject.σ_naturality
-/

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
  SimplexCategory.Truncated n ⥤ C
deriving Category
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
  Comma (const C) (𝟭 (CosimplicialObject C))
deriving Category
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

open scoped Simplicial

#print CategoryTheory.CosimplicialObject.augment /-
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
-/

#print CategoryTheory.CosimplicialObject.augment_hom_zero /-
@[simp]
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) (w) :
    (X.augment X₀ f w).Hom.app [0] = f := by dsimp;
  rw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, category.comp_id]
#align category_theory.cosimplicial_object.augment_hom_zero CategoryTheory.CosimplicialObject.augment_hom_zero
-/

end CosimplicialObject

#print CategoryTheory.simplicialCosimplicialEquiv /-
/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps]
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _
#align category_theory.simplicial_cosimplicial_equiv CategoryTheory.simplicialCosimplicialEquiv
-/

#print CategoryTheory.cosimplicialSimplicialEquiv /-
/-- The anti-equivalence between cosimplicial objects and simplicial objects. -/
@[simps]
def cosimplicialSimplicialEquiv : (CosimplicialObject C)ᵒᵖ ≌ SimplicialObject Cᵒᵖ :=
  Functor.opUnopEquiv _ _
#align category_theory.cosimplicial_simplicial_equiv CategoryTheory.cosimplicialSimplicialEquiv
-/

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

#print CategoryTheory.simplicialCosimplicialAugmentedEquiv /-
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
-/

end CategoryTheory

