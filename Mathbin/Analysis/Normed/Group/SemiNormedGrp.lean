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

#print SemiNormedGrp /-
/-- The category of seminormed abelian groups and bounded group homomorphisms. -/
def SemiNormedGrp : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup SemiNormedGrp
-/

namespace SemiNormedGrp

#print SemiNormedGrp.bundledHom /-
instance bundledHom : BundledHom @NormedAddGroupHom :=
  ⟨@NormedAddGroupHom.toFun, @NormedAddGroupHom.id, @NormedAddGroupHom.comp,
    @NormedAddGroupHom.coe_inj⟩
#align SemiNormedGroup.bundled_hom SemiNormedGrp.bundledHom
-/

deriving instance LargeCategory, ConcreteCategory for SemiNormedGrp

instance : CoeSort SemiNormedGrp (Type u) :=
  Bundled.hasCoeToSort

/- warning: SemiNormedGroup.of clashes with SemiNormedGrp.of -> SemiNormedGrp.of
Case conversion may be inaccurate. Consider using '#align SemiNormedGroup.of SemiNormedGrp.ofₓ'. -/
#print SemiNormedGrp.of /-
/-- Construct a bundled `SemiNormedGroup` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGrp :=
  Bundled.of M
#align SemiNormedGroup.of SemiNormedGrp.of
-/

instance (M : SemiNormedGrp) : SeminormedAddCommGroup M :=
  M.str

#print SemiNormedGrp.coe_of /-
@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp.of V : Type u) = V :=
  rfl
#align SemiNormedGroup.coe_of SemiNormedGrp.coe_of
-/

#print SemiNormedGrp.coe_id /-
@[simp]
theorem coe_id (V : SemiNormedGrp) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup.coe_id SemiNormedGrp.coe_id
-/

#print SemiNormedGrp.coe_comp /-
@[simp]
theorem coe_comp {M N K : SemiNormedGrp} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup.coe_comp SemiNormedGrp.coe_comp
-/

instance : Inhabited SemiNormedGrp :=
  ⟨of PUnit⟩

#print SemiNormedGrp.ofUnique /-
instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGrp.of V) :=
  i
#align SemiNormedGroup.of_unique SemiNormedGrp.ofUnique
-/

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp where

#print SemiNormedGrp.zero_apply /-
@[simp]
theorem zero_apply {V W : SemiNormedGrp} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup.zero_apply SemiNormedGrp.zero_apply
-/

#print SemiNormedGrp.isZero_of_subsingleton /-
theorem isZero_of_subsingleton (V : SemiNormedGrp) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
  · ext; apply Subsingleton.elim
#align SemiNormedGroup.is_zero_of_subsingleton SemiNormedGrp.isZero_of_subsingleton
-/

#print SemiNormedGrp.hasZeroObject /-
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup.has_zero_object SemiNormedGrp.hasZeroObject
-/

#print SemiNormedGrp.iso_isometry_of_normNoninc /-
theorem iso_isometry_of_normNoninc {V W : SemiNormedGrp} (i : V ≅ W) (h1 : i.hom.NormNoninc)
    (h2 : i.inv.NormNoninc) : Isometry i.hom :=
  by
  apply AddMonoidHomClass.isometry_of_norm
  intro v
  apply le_antisymm (h1 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := h2 _
#align SemiNormedGroup.iso_isometry_of_norm_noninc SemiNormedGrp.iso_isometry_of_normNoninc
-/

end SemiNormedGrp

#print SemiNormedGrp₁ /-
/-- `SemiNormedGroup₁` is a type synonym for `SemiNormedGroup`,
which we shall equip with the category structure consisting only of the norm non-increasing maps.
-/
def SemiNormedGrp₁ : Type (u + 1) :=
  Bundled SeminormedAddCommGroup
#align SemiNormedGroup₁ SemiNormedGrp₁
-/

namespace SemiNormedGrp₁

instance : CoeSort SemiNormedGrp₁ (Type u) :=
  Bundled.hasCoeToSort

instance : LargeCategory.{u} SemiNormedGrp₁
    where
  hom X Y := { f : NormedAddGroupHom X Y // f.NormNoninc }
  id X := ⟨NormedAddGroupHom.id X, NormedAddGroupHom.NormNoninc.id⟩
  comp X Y Z f g := ⟨(g : NormedAddGroupHom Y Z).comp (f : NormedAddGroupHom X Y), g.2.comp f.2⟩

#print SemiNormedGrp₁.hom_ext /-
@[ext]
theorem hom_ext {M N : SemiNormedGrp₁} (f g : M ⟶ N) (w : (f : M → N) = (g : M → N)) : f = g :=
  Subtype.eq (NormedAddGroupHom.ext (congr_fun w))
#align SemiNormedGroup₁.hom_ext SemiNormedGrp₁.hom_ext
-/

instance : ConcreteCategory.{u} SemiNormedGrp₁
    where
  forget :=
    { obj := fun X => X
      map := fun X Y f => f }
  forget_faithful := { }

#print SemiNormedGrp₁.of /-
/-- Construct a bundled `SemiNormedGroup₁` from the underlying type and typeclass. -/
def of (M : Type u) [SeminormedAddCommGroup M] : SemiNormedGrp₁ :=
  Bundled.of M
#align SemiNormedGroup₁.of SemiNormedGrp₁.of
-/

instance (M : SemiNormedGrp₁) : SeminormedAddCommGroup M :=
  M.str

#print SemiNormedGrp₁.mkHom /-
/-- Promote a morphism in `SemiNormedGroup` to a morphism in `SemiNormedGroup₁`. -/
def mkHom {M N : SemiNormedGrp} (f : M ⟶ N) (i : f.NormNoninc) :
    SemiNormedGrp₁.of M ⟶ SemiNormedGrp₁.of N :=
  ⟨f, i⟩
#align SemiNormedGroup₁.mk_hom SemiNormedGrp₁.mkHom
-/

#print SemiNormedGrp₁.mkHom_apply /-
@[simp]
theorem mkHom_apply {M N : SemiNormedGrp} (f : M ⟶ N) (i : f.NormNoninc) (x) : mkHom f i x = f x :=
  rfl
#align SemiNormedGroup₁.mk_hom_apply SemiNormedGrp₁.mkHom_apply
-/

#print SemiNormedGrp₁.mkIso /-
/-- Promote an isomorphism in `SemiNormedGroup` to an isomorphism in `SemiNormedGroup₁`. -/
@[simps]
def mkIso {M N : SemiNormedGrp} (f : M ≅ N) (i : f.hom.NormNoninc) (i' : f.inv.NormNoninc) :
    SemiNormedGrp₁.of M ≅ SemiNormedGrp₁.of N
    where
  hom := mkHom f.hom i
  inv := mkHom f.inv i'
  hom_inv_id' := by apply Subtype.eq; exact f.hom_inv_id
  inv_hom_id' := by apply Subtype.eq; exact f.inv_hom_id
#align SemiNormedGroup₁.mk_iso SemiNormedGrp₁.mkIso
-/

instance : HasForget₂ SemiNormedGrp₁ SemiNormedGrp
    where forget₂ :=
    { obj := fun X => X
      map := fun X Y f => f.1 }

#print SemiNormedGrp₁.coe_of /-
@[simp]
theorem coe_of (V : Type u) [SeminormedAddCommGroup V] : (SemiNormedGrp₁.of V : Type u) = V :=
  rfl
#align SemiNormedGroup₁.coe_of SemiNormedGrp₁.coe_of
-/

#print SemiNormedGrp₁.coe_id /-
@[simp]
theorem coe_id (V : SemiNormedGrp₁) : ⇑(𝟙 V) = id :=
  rfl
#align SemiNormedGroup₁.coe_id SemiNormedGrp₁.coe_id
-/

#print SemiNormedGrp₁.coe_comp /-
@[simp]
theorem coe_comp {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) : (f ≫ g : M → K) = g ∘ f :=
  rfl
#align SemiNormedGroup₁.coe_comp SemiNormedGrp₁.coe_comp
-/

-- If `coe_fn_coe_base` fires before `coe_comp`, `coe_comp'` puts us back in normal form.
@[simp]
theorem coe_comp' {M N K : SemiNormedGrp₁} (f : M ⟶ N) (g : N ⟶ K) :
    (f ≫ g : NormedAddGroupHom M K) = (↑g : NormedAddGroupHom N K).comp ↑f :=
  rfl
#align SemiNormedGroup₁.coe_comp' SemiNormedGrp₁.coe_comp'

instance : Inhabited SemiNormedGrp₁ :=
  ⟨of PUnit⟩

#print SemiNormedGrp₁.ofUnique /-
instance ofUnique (V : Type u) [SeminormedAddCommGroup V] [i : Unique V] :
    Unique (SemiNormedGrp₁.of V) :=
  i
#align SemiNormedGroup₁.of_unique SemiNormedGrp₁.ofUnique
-/

instance : Limits.HasZeroMorphisms.{u, u + 1} SemiNormedGrp₁
    where
  Zero X Y := { zero := ⟨0, NormedAddGroupHom.NormNoninc.zero⟩ }
  comp_zero X Y f Z := by ext; rfl
  zero_comp X Y Z f := by ext; simp [coeFn_coe_base']

#print SemiNormedGrp₁.zero_apply /-
@[simp]
theorem zero_apply {V W : SemiNormedGrp₁} (x : V) : (0 : V ⟶ W) x = 0 :=
  rfl
#align SemiNormedGroup₁.zero_apply SemiNormedGrp₁.zero_apply
-/

#print SemiNormedGrp₁.isZero_of_subsingleton /-
theorem isZero_of_subsingleton (V : SemiNormedGrp₁) [Subsingleton V] : Limits.IsZero V :=
  by
  refine' ⟨fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩, fun X => ⟨⟨⟨0⟩, fun f => _⟩⟩⟩
  · ext; have : x = 0 := Subsingleton.elim _ _; simp only [this, map_zero]
    exact map_zero f.1
  · ext; apply Subsingleton.elim
#align SemiNormedGroup₁.is_zero_of_subsingleton SemiNormedGrp₁.isZero_of_subsingleton
-/

#print SemiNormedGrp₁.hasZeroObject /-
instance hasZeroObject : Limits.HasZeroObject SemiNormedGrp₁.{u} :=
  ⟨⟨of PUnit, isZero_of_subsingleton _⟩⟩
#align SemiNormedGroup₁.has_zero_object SemiNormedGrp₁.hasZeroObject
-/

#print SemiNormedGrp₁.iso_isometry /-
theorem iso_isometry {V W : SemiNormedGrp₁} (i : V ≅ W) : Isometry i.hom :=
  by
  change Isometry (i.hom : V →+ W)
  refine' AddMonoidHomClass.isometry_of_norm i.hom _
  intro v
  apply le_antisymm (i.hom.2 v)
  calc
    ‖v‖ = ‖i.inv (i.hom v)‖ := by rw [iso.hom_inv_id_apply]
    _ ≤ ‖i.hom v‖ := i.inv.2 _
#align SemiNormedGroup₁.iso_isometry SemiNormedGrp₁.iso_isometry
-/

end SemiNormedGrp₁

