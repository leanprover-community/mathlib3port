/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca

! This file was ported from Lean 3 source module analysis.normed.group.SemiNormedGroup
! leanprover-community/mathlib commit 44b58b42794e5abe2bf86397c38e26b587e07e59
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.CategoryTheory.Limits.Shapes.ZeroMorphisms
import Mathbin.CategoryTheory.ConcreteCategory.BundledHom
import Mathbin.CategoryTheory.Elementwise

/-!
# The category of seminormed groups

We define `SemiNormedGroup`, the category of seminormed groups and normed group homs between them,
as well as `SemiNormedGroup₁`, the subcategory of norm non-increasing morphisms.
-/


noncomputable section

universe u

open CategoryTheory

/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroupCat : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup SemiNormedGroupCat

namespace SemiNormedGroupCat

instance bundledHom : BundledHom @NormedAddGroupHom :=
  ⟨@NormedAddGroupHom.toFun, @NormedAddGroupHom.id, @NormedAddGroupHom.comp,
    @NormedAddGroupHom.coe_inj⟩
#align SemiNormedGroup.bundled_hom SemiNormedGroupCat.bundledHom

deriving instance LargeCategory, ConcreteCategory for SemiNormedGroupCat

instance : CoeSort SemiNormedGroupCat (Type u) :=
  bundled.has_coe_to_sort

/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroupCat :=
  Bundled.of M
#align SemiNormedGroup.of SemiNormedGroupCat.of

instance (M : SemiNormedGroupCat) : SeminormedAddCommGroup M :=
  M.str

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroupCat.of V : Type u) = V :=
  rfl
#align SemiNormedGroup.coe_of SemiNormedGroupCat.coe_of

@[simp]
theorem coe_id (V : SemiNormedGroupCat) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup.coe_id SemiNormedGroupCat.coe_id

@[simp]
theorem coe_comp {M N K : SemiNormedGroupCat} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup.coe_comp SemiNormedGroupCat.coe_comp

instance : Inhabited SemiNormedGroupCat :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroupCat.of V) :=
  i
#align SemiNormedGroup.of_unique SemiNormedGroupCat.ofUnique

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupCat where

@[simp]
theorem zero_apply {V W : SemiNormedGroupCat} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup.zero_apply SemiNormedGroupCat.zero_apply

theorem is_zero_of_subsingleton (V : SemiNormedGroupCat) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 0 := Subsingleton.elim _ _
    simp only [this, map_zero]
  · ext
    apply Subsingleton.elim
#align SemiNormedGroup.is_zero_of_subsingleton SemiNormedGroupCat.is_zero_of_subsingleton

instance has_zero_object : Limits.HasZeroObject SemiNormedGroupCat.{u} :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩
#align SemiNormedGroup.has_zero_object SemiNormedGroupCat.has_zero_object

theorem iso_isometry_of_norm_noninc {V W : SemiNormedGroupCat} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom :=
  by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := h2 _
    
#align SemiNormedGroup.iso_isometry_of_norm_noninc SemiNormedGroupCat.iso_isometry_of_norm_noninc

end SemiNormedGroupCat

/-- `SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroup₁Cat : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup₁ SemiNormedGroup₁Cat

namespace SemiNormedGroup₁Cat

instance : CoeSort SemiNormedGroup₁Cat (Type u) :=
  bundled.has_coe_to_sort

instance : LargeCategory.{u} SemiNormedGroup₁Cat
    where
  hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp X Y Z f g := ⟨(g : NormedAddGroupHom Y Z).comp (f : NormedAddGroupHom X Y), g.2.comp f.2⟩

@[ext]
theorem hom_ext {M N : SemiNormedGroup₁Cat} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) : f = g :=
  Subtype.eq (NormedAddGroupHom.ext (congr_fun w))
#align SemiNormedGroup₁.hom_ext SemiNormedGroup₁Cat.hom_ext

instance : ConcreteCategory.{u} SemiNormedGroup₁Cat
    where
  forget :=
    { obj := fun X => X
      map := fun X Y f => f }
  forget_faithful := { }

/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroup₁Cat :=
  Bundled.of M
#align SemiNormedGroup₁.of SemiNormedGroup₁Cat.of

instance (M : SemiNormedGroup₁Cat) : SeminormedAddCommGroup M :=
  M.str

/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mkHom {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGroup₁Cat.of M ⟶ SemiNormedGroup₁Cat.of N :=
  ⟨f, i⟩
#align SemiNormedGroup₁.mk_hom SemiNormedGroup₁Cat.mkHom

@[simp]
theorem mk_hom_apply {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl
#align SemiNormedGroup₁.mk_hom_apply SemiNormedGroup₁Cat.mk_hom_apply

/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mkIso {M N : SemiNormedGroupCat} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGroup₁Cat.of M ≅ SemiNormedGroup₁Cat.of N
    where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id' := by
    apply Subtype.eq
    exact f.hom_inv_id
  inv_hom_id' := by
    apply Subtype.eq
    exact f.inv_hom_id
#align SemiNormedGroup₁.mk_iso SemiNormedGroup₁Cat.mkIso

instance : HasForget₂ SemiNormedGroup₁Cat SemiNormedGroupCat
    where forget₂ :=
    { obj := fun X => X
      map := fun X Y f => f.1 }

@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroup₁Cat.of V : Type u) = V :=
  rfl
#align SemiNormedGroup₁.coe_of SemiNormedGroup₁Cat.coe_of

@[simp]
theorem coe_id (V : SemiNormedGroup₁Cat) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup₁.coe_id SemiNormedGroup₁Cat.coe_id

@[simp]
theorem coe_comp {M N K : SemiNormedGroup₁Cat} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup₁.coe_comp SemiNormedGroup₁Cat.coe_comp

-- If `coe_fn_coe_base` fires before `coe_comp`, `coe_comp'` puts us back in normal form.
@[simp]
theorem coe_comp' {M N K : SemiNormedGroup₁Cat} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : NormedAddGroupHom M K) = (↑g : NormedAddGroupHom N K).comp ↑f :=
  rfl
#align SemiNormedGroup₁.coe_comp' SemiNormedGroup₁Cat.coe_comp'

instance : Inhabited SemiNormedGroup₁Cat :=
  ⟨of PUnit⟩

instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroup₁Cat.of V) :=
  i
#align SemiNormedGroup₁.of_unique SemiNormedGroup₁Cat.ofUnique

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroup₁Cat
    where
  HasZero X Y := { zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩ }
  comp_zero' X Y f Z := by
    ext
    rfl
  zero_comp' X Y Z f := by
    ext
    simp [coe_fn_coe_base']

@[simp]
theorem zero_apply {V W : SemiNormedGroup₁Cat} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup₁.zero_apply SemiNormedGroup₁Cat.zero_apply

theorem is_zero_of_subsingleton (V : SemiNormedGroup₁Cat) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext
    have : x = 0 := Subsingleton.elim _ _
    simp only [this, map_zero]
    exact map_zero f.1
  · ext
    apply Subsingleton.elim
#align SemiNormedGroup₁.is_zero_of_subsingleton SemiNormedGroup₁Cat.is_zero_of_subsingleton

instance has_zero_object : Limits.HasZeroObject SemiNormedGroup₁Cat.{u} :=
  ⟨⟨of PUnit, is_zero_of_subsingleton _⟩⟩
#align SemiNormedGroup₁.has_zero_object SemiNormedGroup₁Cat.has_zero_object

theorem iso_isometry {V W : SemiNormedGroup₁Cat} (i : V ≅ W) : Isometry i.hom :=
  by
  change Isometry (i.hom : V →+ W)
  refine' AddMonoidHomClass.isometry_of_norm i.hom _
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _
    
#align SemiNormedGroup₁.iso_isometry SemiNormedGroup₁Cat.iso_isometry

end SemiNormedGroup₁Cat

