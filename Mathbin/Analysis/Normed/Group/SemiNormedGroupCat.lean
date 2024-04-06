/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Riccardo Brasca
-/
import Analysis.Normed.Group.Hom
import CategoryTheory.Limits.Shapes.ZeroMorphisms
import CategoryTheory.ConcreteCategory.BundledHom
import CategoryTheory.Elementwise

#align_import analysis.normed.group.SemiNormedGroup from "leanprover-community/mathlib"@"cff8231f04dfa33fd8f2f45792eebd862ef30cad"

/-!
# The category of seminormed groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We define `SemiNormedGroup`, the category of seminormed groups and normed group homs between them,
as well as `SemiNormedGroup₁`, the subcategory of norm non-increasing morphisms.
-/


noncomputable section

universe u

open CategoryTheory

#print SemiNormedGroupCat /-
/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGroupCat : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup SemiNormedGroupCat
-/

namespace SemiNormedGroupCat

#print SemiNormedGroupCat.bundledHom /-
instance bundledHom : BundledHom @NormedAddGroupHom :=
  ⟨@NormedAddGroupHom.toFun, @NormedAddGroupHom.id, @NormedAddGroupHom.comp,
    @NormedAddGroupHom.coe_inj⟩
#align SemiNormedGroup.bundled_hom SemiNormedGroupCat.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for SemiNormedGroupCat

instance : CoeSort SemiNormedGroupCat (Type u) :=
  Bundled.hasCoeToSort

/- warning: SemiNormedGroup.of clashes with SemiNormedGroupCat.of -> SemiNormedGroupCat.of
Case conversion may be inaccurate. Consider using '#align SemiNormedGroup.of SemiNormedGroupCat.ofₓ'. -/
#print SemiNormedGroupCat.of /-
/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroupCat :=
  Bundled.of M
#align SemiNormedGroup.of SemiNormedGroupCat.of
-/

instance (M : SemiNormedGroupCat) : SeminormedAddCommGroup M :=
  M.str

#print SemiNormedGroupCat.coe_of /-
@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroupCat.of V : Type u) = V :=
  rfl
#align SemiNormedGroup.coe_of SemiNormedGroupCat.coe_of
-/

#print SemiNormedGroupCat.coe_id /-
@[simp]
theorem coe_id (V : SemiNormedGroupCat) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup.coe_id SemiNormedGroupCat.coe_id
-/

#print SemiNormedGroupCat.coe_comp /-
@[simp]
theorem coe_comp {M N K : SemiNormedGroupCat} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup.coe_comp SemiNormedGroupCat.coe_comp
-/

instance : Inhabited SemiNormedGroupCat :=
  ⟨of PUnit⟩

#print SemiNormedGroupCat.ofUnique /-
instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroupCat.of V) :=
  i
#align SemiNormedGroup.of_unique SemiNormedGroupCat.ofUnique
-/

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupCat where

#print SemiNormedGroupCat.zero_apply /-
@[simp]
theorem zero_apply {V W : SemiNormedGroupCat} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup.zero_apply SemiNormedGroupCat.zero_apply
-/

#print SemiNormedGroupCat.isZero_of_subsingleton /-
theorem isZero_of_subsingleton (V : SemiNormedGroupCat) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim
#align SemiNormedGroup.is_zero_of_subsingleton SemiNormedGroupCat.isZero_of_subsingleton
-/

#print SemiNormedGroupCat.hasZeroObject /-
instance hasZeroObject : Limits.HasZeroObject SemiNormedGroupCat.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup.has_zero_object SemiNormedGroupCat.hasZeroObject
-/

#print SemiNormedGroupCat.iso_isometry_of_normNoninc /-
theorem iso_isometry_of_normNoninc {V W : SemiNormedGroupCat} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom :=
  by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := h2 _
#align SemiNormedGroup.iso_isometry_of_norm_noninc SemiNormedGroupCat.iso_isometry_of_normNoninc
-/

end SemiNormedGroupCat

#print SemiNormedGroupCat₁ /-
/-- `SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGroupCat₁ : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup₁ SemiNormedGroupCat₁
-/

namespace SemiNormedGroupCat₁

instance : CoeSort SemiNormedGroupCat₁ (Type u) :=
  Bundled.hasCoeToSort

instance : LargeCategory.{u} SemiNormedGroupCat₁
    where
  hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp X Y Z f g := ⟨(g : NormedAddGroupHom Y Z).comp (f : NormedAddGroupHom X Y), g.2.comp f.2⟩

#print SemiNormedGroupCat₁.hom_ext /-
@[ext]
theorem hom_ext {M N : SemiNormedGroupCat₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) : f = g :=
  Subtype.eq (NormedAddGroupHom.ext (congr_fun w))
#align SemiNormedGroup₁.hom_ext SemiNormedGroupCat₁.hom_ext
-/

instance : ConcreteCategory.{u} SemiNormedGroupCat₁
    where
  forget :=
    { obj := fun X => X
      map := fun X Y f => f }
  forget_faithful := { }

#print SemiNormedGroupCat₁.of /-
/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGroupCat₁ :=
  Bundled.of M
#align SemiNormedGroup₁.of SemiNormedGroupCat₁.of
-/

instance (M : SemiNormedGroupCat₁) : SeminormedAddCommGroup M :=
  M.str

#print SemiNormedGroupCat₁.mkHom /-
/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mkHom {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGroupCat₁.of M ⟶ SemiNormedGroupCat₁.of N :=
  ⟨f, i⟩
#align SemiNormedGroup₁.mk_hom SemiNormedGroupCat₁.mkHom
-/

#print SemiNormedGroupCat₁.mkHom_apply /-
@[simp]
theorem mkHom_apply {M N : SemiNormedGroupCat} (f : M ⟶ N) (i : f.NormNoninc) (x) :
    mkHom f i x = f x :=
  rfl
#align SemiNormedGroup₁.mk_hom_apply SemiNormedGroupCat₁.mkHom_apply
-/

#print SemiNormedGroupCat₁.mkIso /-
/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mkIso {M N : SemiNormedGroupCat} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGroupCat₁.of M ≅ SemiNormedGroupCat₁.of N
    where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id' := by apply Subtype.eq; exact f.hom_inv_id
  inv_hom_id' := by apply Subtype.eq; exact f.inv_hom_id
#align SemiNormedGroup₁.mk_iso SemiNormedGroupCat₁.mkIso
-/

instance : HasForget₂ SemiNormedGroupCat₁ SemiNormedGroupCat
    where forget₂ :=
    { obj := fun X => X
      map := fun X Y f => f.1 }

#print SemiNormedGroupCat₁.coe_of /-
@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGroupCat₁.of V : Type u) = V :=
  rfl
#align SemiNormedGroup₁.coe_of SemiNormedGroupCat₁.coe_of
-/

#print SemiNormedGroupCat₁.coe_id /-
@[simp]
theorem coe_id (V : SemiNormedGroupCat₁) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup₁.coe_id SemiNormedGroupCat₁.coe_id
-/

#print SemiNormedGroupCat₁.coe_comp /-
@[simp]
theorem coe_comp {M N K : SemiNormedGroupCat₁} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup₁.coe_comp SemiNormedGroupCat₁.coe_comp
-/

-- If `coe_fn_coe_base` fires before `coe_comp`, `coe_comp'` puts us back in normal form.
@[simp]
theorem coe_comp' {M N K : SemiNormedGroupCat₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : NormedAddGroupHom M K) = (↑g : NormedAddGroupHom N K).comp ↑f :=
  rfl
#align SemiNormedGroup₁.coe_comp' SemiNormedGroupCat₁.coe_comp'

instance : Inhabited SemiNormedGroupCat₁ :=
  ⟨of PUnit⟩

#print SemiNormedGroupCat₁.ofUnique /-
instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGroupCat₁.of V) :=
  i
#align SemiNormedGroup₁.of_unique SemiNormedGroupCat₁.ofUnique
-/

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGroupCat₁
    where
  Zero X Y := { zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩ }
  comp_zero X Y f Z := by ext; rfl
  zero_comp X Y Z f := by ext; simp [coeFn_coe_base']

#print SemiNormedGroupCat₁.zero_apply /-
@[simp]
theorem zero_apply {V W : SemiNormedGroupCat₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup₁.zero_apply SemiNormedGroupCat₁.zero_apply
-/

#print SemiNormedGroupCat₁.isZero_of_subsingleton /-
theorem isZero_of_subsingleton (V : SemiNormedGroupCat₁) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
    exact map_zero f.1
  · ext; apply Subsingleton.elim
#align SemiNormedGroup₁.is_zero_of_subsingleton SemiNormedGroupCat₁.isZero_of_subsingleton
-/

#print SemiNormedGroupCat₁.hasZeroObject /-
instance hasZeroObject : Limits.HasZeroObject SemiNormedGroupCat₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup₁.has_zero_object SemiNormedGroupCat₁.hasZeroObject
-/

#print SemiNormedGroupCat₁.iso_isometry /-
theorem iso_isometry {V W : SemiNormedGroupCat₁} (i : V ≅ W) : Isometry i.hom :=
  by
  change Isometry (i.hom : V →+ W)
  refine' AddMonoidHomClass.isometry_of_norm i.hom _
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _
#align SemiNormedGroup₁.iso_isometry SemiNormedGroupCat₁.iso_isometry
-/

end SemiNormedGroupCat₁

