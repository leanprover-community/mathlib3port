/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Scott Morrison, Adam Topaz
-/
import Mathbin.AlgebraicTopology.SimplexCategory
import Mathbin.CategoryTheory.Arrow
import Mathbin.CategoryTheory.Limits.FunctorCategory
import Mathbin.CategoryTheory.Opposites

/-!
# Simplicial objects in a category.

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

/-- The category of simplicial objects valued in a category `C`.
This is the category of contravariant functors from `simplex_category` to `C`. -/
@[nolint has_inhabited_instance]
def SimplicialObject :=
  SimplexCategoryᵒᵖ ⥤ C deriving Category

namespace SimplicialObject

-- mathport name: «expr _[ ]»
localized [Simplicial]
  notation:1000 X "_[" n "]" => (X : CategoryTheory.SimplicialObject _).obj (Opposite.op (SimplexCategory.mk n))

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] : HasLimitsOfShape J (SimplicialObject C) := by
  dsimp [simplicial_object]
  infer_instance

instance [HasLimits C] : HasLimits (SimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] : HasColimitsOfShape J (SimplicialObject C) := by
  dsimp [simplicial_object]
  infer_instance

instance [HasColimits C] : HasColimits (SimplicialObject C) :=
  ⟨inferInstance⟩

variable {C} (X : SimplicialObject C)

/-- Face maps for a simplicial object. -/
def δ {n} (i : Finₓ (n + 2)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.δ i).op

/-- Degeneracy maps for a simplicial object. -/
def σ {n} (i : Finₓ (n + 1)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.σ i).op

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso
    (eqToIso
      (by
        rw [h]))

@[simp]
theorem eq_to_iso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  simp [eq_to_iso]

/-- The generic case of the first simplicial identity -/
theorem δ_comp_δ {n} {i j : Finₓ (n + 2)} (H : i ≤ j) : X.δ j.succ ≫ X.δ i = X.δ i.cast_succ ≫ X.δ j := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ H]

/-- The special case of the first simplicial identity -/
theorem δ_comp_δ_self {n} {i : Finₓ (n + 2)} : X.δ i.cast_succ ≫ X.δ i = X.δ i.succ ≫ X.δ i := by
  dsimp [δ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_δ_self]

/-- The second simplicial identity -/
theorem δ_comp_σ_of_le {n} {i : Finₓ (n + 2)} {j : Finₓ (n + 1)} (H : i ≤ j.cast_succ) :
    X.σ j.succ ≫ X.δ i.cast_succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third simplicial identity -/
theorem δ_comp_σ_self {n} {i : Finₓ (n + 1)} : X.σ i ≫ X.δ i.cast_succ = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_self, op_id, X.map_id]

/-- The second part of the third simplicial identity -/
theorem δ_comp_σ_succ {n} {i : Finₓ (n + 1)} : X.σ i ≫ X.δ i.succ = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_succ, op_id, X.map_id]

/-- The fourth simplicial identity -/
theorem δ_comp_σ_of_gt {n} {i : Finₓ (n + 2)} {j : Finₓ (n + 1)} (H : j.cast_succ < i) :
    X.σ j.cast_succ ≫ X.δ i.succ = X.δ i ≫ X.σ j := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.δ_comp_σ_of_gt H]

/-- The fifth simplicial identity -/
theorem σ_comp_σ {n} {i j : Finₓ (n + 1)} (H : i ≤ j) : X.σ j ≫ X.σ i.cast_succ = X.σ i ≫ X.σ j.succ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, ← op_comp, SimplexCategory.σ_comp_σ H]

variable (C)

/-- Functor composition induces a functor on simplicial objects. -/
@[simps]
def whiskering (D : Type _) [Category D] : (C ⥤ D) ⥤ SimplicialObject C ⥤ SimplicialObject D :=
  whiskeringRight _ _ _

/-- Truncated simplicial objects. -/
@[nolint has_inhabited_instance]
def Truncated (n : ℕ) :=
  (SimplexCategory.Truncated n)ᵒᵖ ⥤ C deriving Category

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (SimplicialObject.Truncated C n) := by
  dsimp [truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (SimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

/-- Functor composition induces a functor on truncated simplicial objects. -/
@[simps]
def whiskering {n} (D : Type _) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

variable {C}

end Truncated

section Skeleton

/-- The skeleton functor from simplicial objects to truncated simplicial objects. -/
def sk (n : ℕ) : SimplicialObject C ⥤ SimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion.op

end Skeleton

variable (C)

/-- The constant simplicial object is the constant functor. -/
abbrev const : C ⥤ SimplicialObject C :=
  CategoryTheory.Functor.const _

/-- The category of augmented simplicial objects, defined as a comma category. -/
@[nolint has_inhabited_instance]
def Augmented :=
  Comma (𝟭 (SimplicialObject C)) (const C)deriving Category

variable {C}

namespace Augmented

/-- Drop the augmentation. -/
@[simps]
def drop : Augmented C ⥤ SimplicialObject C :=
  Comma.fst _ _

/-- The point of the augmentation. -/
@[simps]
def point : Augmented C ⥤ C :=
  Comma.snd _ _

/-- The functor from augmented objects to arrows. -/
@[simps]
def toArrow : Augmented C ⥤ Arrow C where
  obj := fun X => { left := drop.obj X _[0], right := point.obj X, Hom := X.Hom.app _ }
  map := fun X Y η =>
    { left := (drop.map η).app _, right := point.map η,
      w' := by
        dsimp
        rw [← nat_trans.comp_app]
        erw [η.w]
        rfl }

variable (C)

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simp]
def whiskeringObj (D : Type _) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj := fun X =>
    { left := ((whiskering _ _).obj F).obj (drop.obj X), right := F.obj (point.obj X),
      Hom := whiskerRight X.Hom F ≫ (Functor.constComp _ _ _).Hom }
  map := fun X Y η =>
    { left := whiskerRight η.left _, right := F.map η.right,
      w' := by
        ext
        dsimp
        erw [category.comp_id, category.comp_id, ← F.map_comp, ← F.map_comp, ← nat_trans.comp_app, η.w]
        rfl }

/-- Functor composition induces a functor on augmented simplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map := fun X Y η =>
    { app := fun A =>
        { left := whiskerLeft _ η, right := η.app _,
          w' := by
            ext n
            dsimp
            erw [category.comp_id, category.comp_id, η.naturality] } }

variable {C}

end Augmented

open Simplicial

/-- Aaugment a simplicial object with an object. -/
@[simps]
def augment (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀)
    (w : ∀ i : SimplexCategory g₁ g₂ : [0] ⟶ i, X.map g₁.op ≫ f = X.map g₂.op ≫ f) : SimplicialObject.Augmented C where
  left := X
  right := X₀
  Hom :=
    { app := fun i => X.map (SimplexCategory.const i.unop 0).op ≫ f,
      naturality' := by
        intro i j g
        dsimp
        rw [← g.op_unop]
        simpa only [← X.map_comp, ← category.assoc, category.comp_id, ← op_comp] using w _ _ _ }

@[simp]
theorem augment_hom_zero (X : SimplicialObject C) (X₀ : C) (f : X _[0] ⟶ X₀) w :
    (X.augment X₀ f w).Hom.app (op [0]) = f := by
  dsimp
  erw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, category.id_comp]

end SimplicialObject

/-- Cosimplicial objects. -/
@[nolint has_inhabited_instance]
def CosimplicialObject :=
  SimplexCategory ⥤ C deriving Category

namespace CosimplicialObject

-- mathport name: «expr _[ ]»
localized [Simplicial]
  notation:1000 X "_[" n "]" => (X : CategoryTheory.CosimplicialObject _).obj (SimplexCategory.mk n)

instance {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] : HasLimitsOfShape J (CosimplicialObject C) := by
  dsimp [cosimplicial_object]
  infer_instance

instance [HasLimits C] : HasLimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

instance {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] : HasColimitsOfShape J (CosimplicialObject C) := by
  dsimp [cosimplicial_object]
  infer_instance

instance [HasColimits C] : HasColimits (CosimplicialObject C) :=
  ⟨inferInstance⟩

variable {C} (X : CosimplicialObject C)

/-- Coface maps for a cosimplicial object. -/
def δ {n} (i : Finₓ (n + 2)) : X _[n] ⟶ X _[n + 1] :=
  X.map (SimplexCategory.δ i)

/-- Codegeneracy maps for a cosimplicial object. -/
def σ {n} (i : Finₓ (n + 1)) : X _[n + 1] ⟶ X _[n] :=
  X.map (SimplexCategory.σ i)

/-- Isomorphisms from identities in ℕ. -/
def eqToIso {n m : ℕ} (h : n = m) : X _[n] ≅ X _[m] :=
  X.mapIso
    (eqToIso
      (by
        rw [h]))

@[simp]
theorem eq_to_iso_refl {n : ℕ} (h : n = n) : X.eqToIso h = Iso.refl _ := by
  ext
  simp [eq_to_iso]

/-- The generic case of the first cosimplicial identity -/
theorem δ_comp_δ {n} {i j : Finₓ (n + 2)} (H : i ≤ j) : X.δ i ≫ X.δ j.succ = X.δ j ≫ X.δ i.cast_succ := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ H]

/-- The special case of the first cosimplicial identity -/
theorem δ_comp_δ_self {n} {i : Finₓ (n + 2)} : X.δ i ≫ X.δ i.cast_succ = X.δ i ≫ X.δ i.succ := by
  dsimp [δ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_δ_self]

/-- The second cosimplicial identity -/
theorem δ_comp_σ_of_le {n} {i : Finₓ (n + 2)} {j : Finₓ (n + 1)} (H : i ≤ j.cast_succ) :
    X.δ i.cast_succ ≫ X.σ j.succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_le H]

/-- The first part of the third cosimplicial identity -/
theorem δ_comp_σ_self {n} {i : Finₓ (n + 1)} : X.δ i.cast_succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_self, X.map_id]

/-- The second part of the third cosimplicial identity -/
theorem δ_comp_σ_succ {n} {i : Finₓ (n + 1)} : X.δ i.succ ≫ X.σ i = 𝟙 _ := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_succ, X.map_id]

/-- The fourth cosimplicial identity -/
theorem δ_comp_σ_of_gt {n} {i : Finₓ (n + 2)} {j : Finₓ (n + 1)} (H : j.cast_succ < i) :
    X.δ i.succ ≫ X.σ j.cast_succ = X.σ j ≫ X.δ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.δ_comp_σ_of_gt H]

/-- The fifth cosimplicial identity -/
theorem σ_comp_σ {n} {i j : Finₓ (n + 1)} (H : i ≤ j) : X.σ i.cast_succ ≫ X.σ j = X.σ j.succ ≫ X.σ i := by
  dsimp [δ, σ]
  simp only [← X.map_comp, SimplexCategory.σ_comp_σ H]

variable (C)

/-- Functor composition induces a functor on cosimplicial objects. -/
@[simps]
def whiskering (D : Type _) [Category D] : (C ⥤ D) ⥤ CosimplicialObject C ⥤ CosimplicialObject D :=
  whiskeringRight _ _ _

/-- Truncated cosimplicial objects. -/
@[nolint has_inhabited_instance]
def Truncated (n : ℕ) :=
  SimplexCategory.Truncated n ⥤ C deriving Category

variable {C}

namespace Truncated

instance {n} {J : Type v} [SmallCategory J] [HasLimitsOfShape J C] :
    HasLimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [truncated]
  infer_instance

instance {n} [HasLimits C] : HasLimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

instance {n} {J : Type v} [SmallCategory J] [HasColimitsOfShape J C] :
    HasColimitsOfShape J (CosimplicialObject.Truncated C n) := by
  dsimp [truncated]
  infer_instance

instance {n} [HasColimits C] : HasColimits (CosimplicialObject.Truncated C n) :=
  ⟨inferInstance⟩

variable (C)

/-- Functor composition induces a functor on truncated cosimplicial objects. -/
@[simps]
def whiskering {n} (D : Type _) [Category D] : (C ⥤ D) ⥤ Truncated C n ⥤ Truncated D n :=
  whiskeringRight _ _ _

variable {C}

end Truncated

section Skeleton

/-- The skeleton functor from cosimplicial objects to truncated cosimplicial objects. -/
def sk (n : ℕ) : CosimplicialObject C ⥤ CosimplicialObject.Truncated C n :=
  (whiskeringLeft _ _ _).obj SimplexCategory.Truncated.inclusion

end Skeleton

variable (C)

/-- The constant cosimplicial object. -/
abbrev const : C ⥤ CosimplicialObject C :=
  CategoryTheory.Functor.const _

/-- Augmented cosimplicial objects. -/
@[nolint has_inhabited_instance]
def Augmented :=
  Comma (const C) (𝟭 (CosimplicialObject C))deriving Category

variable {C}

namespace Augmented

/-- Drop the augmentation. -/
@[simps]
def drop : Augmented C ⥤ CosimplicialObject C :=
  Comma.snd _ _

/-- The point of the augmentation. -/
@[simps]
def point : Augmented C ⥤ C :=
  Comma.fst _ _

/-- The functor from augmented objects to arrows. -/
@[simps]
def toArrow : Augmented C ⥤ Arrow C where
  obj := fun X => { left := point.obj X, right := drop.obj X _[0], Hom := X.Hom.app _ }
  map := fun X Y η =>
    { left := point.map η, right := (drop.map η).app _,
      w' := by
        dsimp
        rw [← nat_trans.comp_app]
        erw [← η.w]
        rfl }

variable (C)

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simp]
def whiskeringObj (D : Type _) [Category D] (F : C ⥤ D) : Augmented C ⥤ Augmented D where
  obj := fun X =>
    { left := F.obj (point.obj X), right := ((whiskering _ _).obj F).obj (drop.obj X),
      Hom := (Functor.constComp _ _ _).inv ≫ whiskerRight X.Hom F }
  map := fun X Y η =>
    { left := F.map η.left, right := whiskerRight η.right _,
      w' := by
        ext
        dsimp
        erw [category.id_comp, category.id_comp, ← F.map_comp, ← F.map_comp, ← nat_trans.comp_app, ← η.w]
        rfl }

/-- Functor composition induces a functor on augmented cosimplicial objects. -/
@[simps]
def whiskering (D : Type u') [Category.{v'} D] : (C ⥤ D) ⥤ Augmented C ⥤ Augmented D where
  obj := whiskeringObj _ _
  map := fun X Y η =>
    { app := fun A =>
        { left := η.app _, right := whiskerLeft _ η,
          w' := by
            ext n
            dsimp
            erw [category.id_comp, category.id_comp, η.naturality] } }

variable {C}

end Augmented

open Simplicial

/-- Augment a cosimplicial object with an object. -/
@[simps]
def augment (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0])
    (w : ∀ i : SimplexCategory g₁ g₂ : [0] ⟶ i, f ≫ X.map g₁ = f ≫ X.map g₂) : CosimplicialObject.Augmented C where
  left := X₀
  right := X
  Hom :=
    { app := fun i => f ≫ X.map (SimplexCategory.const i 0),
      naturality' := by
        intro i j g
        dsimp
        simpa [← X.map_comp] using w _ _ _ }

@[simp]
theorem augment_hom_zero (X : CosimplicialObject C) (X₀ : C) (f : X₀ ⟶ X.obj [0]) w :
    (X.augment X₀ f w).Hom.app [0] = f := by
  dsimp
  rw [SimplexCategory.hom_zero_zero ([0].const 0), X.map_id, category.comp_id]

end CosimplicialObject

/-- The anti-equivalence between simplicial objects and cosimplicial objects. -/
@[simps]
def simplicialCosimplicialEquiv : (SimplicialObject C)ᵒᵖ ≌ CosimplicialObject Cᵒᵖ :=
  Functor.leftOpRightOpEquiv _ _

variable {C}

/-- Construct an augmented cosimplicial object in the opposite
category from an augmented simplicial object. -/
@[simps]
def SimplicialObject.Augmented.rightOp (X : SimplicialObject.Augmented C) : CosimplicialObject.Augmented Cᵒᵖ where
  left := Opposite.op X.right
  right := X.left.rightOp
  Hom := X.Hom.rightOp

/-- Construct an augmented simplicial object from an augmented cosimplicial
object in the opposite category. -/
@[simps]
def CosimplicialObject.Augmented.leftOp (X : CosimplicialObject.Augmented Cᵒᵖ) : SimplicialObject.Augmented C where
  left := X.right.leftOp
  right := X.left.unop
  Hom := X.Hom.leftOp

/-- Converting an augmented simplicial object to an augmented cosimplicial
object and back is isomorphic to the given object. -/
@[simps]
def SimplicialObject.Augmented.rightOpLeftOpIso (X : SimplicialObject.Augmented C) : X.rightOp.leftOp ≅ X :=
  Comma.isoMk X.left.rightOpLeftOpIso
    (eq_to_iso <| by
      simp )
    (by
      tidy)

/-- Converting an augmented cosimplicial object to an augmented simplicial
object and back is isomorphic to the given object. -/
@[simps]
def CosimplicialObject.Augmented.leftOpRightOpIso (X : CosimplicialObject.Augmented Cᵒᵖ) : X.leftOp.rightOp ≅ X :=
  Comma.isoMk
    (eq_to_iso <| by
      simp )
    X.right.leftOpRightOpIso
    (by
      tidy)

variable (C)

/-- A functorial version of `simplicial_object.augmented.right_op`. -/
@[simps]
def simplicialToCosimplicialAugmented : (SimplicialObject.Augmented C)ᵒᵖ ⥤ CosimplicialObject.Augmented Cᵒᵖ where
  obj := fun X => X.unop.rightOp
  map := fun X Y f =>
    { left := f.unop.right.op, right := f.unop.left.rightOp,
      w' := by
        ext x
        dsimp
        simp_rw [← op_comp]
        congr 1
        exact (congr_app f.unop.w (op x)).symm }

/-- A functorial version of `cosimplicial_object.augmented.left_op`. -/
@[simps]
def cosimplicialToSimplicialAugmented : CosimplicialObject.Augmented Cᵒᵖ ⥤ (SimplicialObject.Augmented C)ᵒᵖ where
  obj := fun X => Opposite.op X.leftOp
  map := fun X Y f =>
    Quiver.Hom.op <|
      { left := f.right.leftOp, right := f.left.unop,
        w' := by
          ext x
          dsimp
          simp_rw [← unop_comp]
          congr 1
          exact (congr_app f.w x.unop).symm }

/-- The contravariant categorical equivalence between augmented simplicial
objects and augmented cosimplicial objects in the opposite category. -/
@[simps]
def simplicialCosimplicialAugmentedEquiv : (SimplicialObject.Augmented C)ᵒᵖ ≌ CosimplicialObject.Augmented Cᵒᵖ where
  Functor := simplicialToCosimplicialAugmented _
  inverse := cosimplicialToSimplicialAugmented _
  unitIso :=
    NatIso.ofComponents (fun X => X.unop.rightOpLeftOpIso.op)
      (by
        intro X Y f
        dsimp
        rw
          [show f = f.unop.op by
            simp ]
        simp_rw [← op_comp]
        congr 1
        tidy)
  counitIso :=
    NatIso.ofComponents (fun X => X.leftOpRightOpIso)
      (by
        tidy)

end CategoryTheory

