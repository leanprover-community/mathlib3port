/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.CategoryTheory.Limits.Shapes.Biproducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Zero
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Preservation of biproducts

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `preserves_biproduct` and `preserves_binary_biproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* construct the comparison morphisms between the image of a biproduct and the biproduct of the
  images and show that the biproduct is preserved if one of them is an isomorphism,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images
  in case that the biproduct is preserved.

-/


universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

section Map

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁}

/-- The image of a bicone under a functor. -/
@[simps]
def mapBicone {f : J → C} (b : Bicone f) : Bicone (F.obj ∘ f) where
  x := F.obj b.x
  π j := F.map (b.π j)
  ι j := F.map (b.ι j)
  ι_π j j' := by
    rw [← F.map_comp]
    split_ifs
    · subst h
      simp only [bicone_ι_π_self, CategoryTheory.Functor.map_id, eq_to_hom_refl]
      
    · rw [bicone_ι_π_ne _ h, F.map_zero]
      

theorem map_bicone_whisker {K : Type w₂} {g : K ≃ J} {f : J → C} (c : Bicone f) :
    F.mapBicone (c.whisker g) = (F.mapBicone c).whisker g :=
  rfl

end Bicone

/-- The image of a binary bicone under a functor. -/
@[simps]
def mapBinaryBicone {X Y : C} (b : BinaryBicone X Y) : BinaryBicone (F.obj X) (F.obj Y) where
  x := F.obj b.x
  fst := F.map b.fst
  snd := F.map b.snd
  inl := F.map b.inl
  inr := F.map b.inr
  inl_fst' := by rw [← F.map_comp, b.inl_fst, F.map_id]
  inl_snd' := by rw [← F.map_comp, b.inl_snd, F.map_zero]
  inr_fst' := by rw [← F.map_comp, b.inr_fst, F.map_zero]
  inr_snd' := by rw [← F.map_comp, b.inr_snd, F.map_id]

end Map

end Functor

open CategoryTheory.Functor

namespace Limits

section Bicone

variable {J : Type w₁} {K : Type w₂}

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
class PreservesBiproduct (f : J → C) (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {b : Bicone f}, b.IsBilimit → (F.mapBicone b).IsBilimit

/-- A functor `F` preserves biproducts of `f` if `F` maps every bilimit bicone over `f` to a
    bilimit bicone over `F.obj ∘ f`. -/
def isBilimitOfPreserves {f : J → C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBiproduct f F] {b : Bicone f}
    (hb : b.IsBilimit) : (F.mapBicone b).IsBilimit :=
  PreservesBiproduct.preserves hb

variable (J)

/-- A functor `F` preserves biproducts of shape `J` if it preserves biproducts of `f` for every
    `f : J → C`. -/
class PreservesBiproductsOfShape (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {f : J → C}, PreservesBiproduct f F

attribute [instance] preserves_biproducts_of_shape.preserves

end Bicone

/-- A functor `F` preserves finite biproducts if it preserves biproducts of shape `J` whenever
    `J` is a fintype. -/
class PreservesFiniteBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {J : Type} [Fintype J], PreservesBiproductsOfShape J F

attribute [instance] preserves_finite_biproducts.preserves

/-- A functor `F` preserves biproducts if it preserves biproducts of any shape `J` of size `w`.
    The usual notion of preservation of biproducts is recovered by choosing `w` to be the universe
    of the morphisms of `C`. -/
class PreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {J : Type w₁}, PreservesBiproductsOfShape J F

attribute [instance] preserves_biproducts.preserves

/-- Preserving biproducts at a bigger universe level implies preserving biproducts at a
smaller universe level. -/
def preservesBiproductsShrink (F : C ⥤ D) [PreservesZeroMorphisms F] [hp : PreservesBiproducts.{max w₁ w₂} F] :
    PreservesBiproducts.{w₁} F :=
  ⟨fun J =>
    ⟨fun f =>
      ⟨fun b ib =>
        ((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩

instance (priority := 100) preservesFiniteBiproductsOfPreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproducts.{w₁} F] :
    PreservesFiniteBiproducts F where preserves J _ := by letI := preservesBiproductsShrink.{0} F <;> infer_instance

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
class PreservesBinaryBiproduct (X Y : C) (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {b : BinaryBicone X Y}, b.IsBilimit → (F.mapBinaryBicone b).IsBilimit

/-- A functor `F` preserves binary biproducts of `X` and `Y` if `F` maps every bilimit bicone over
    `X` and `Y` to a bilimit bicone over `F.obj X` and `F.obj Y`. -/
def isBinaryBilimitOfPreserves {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBinaryBiproduct X Y F]
    {b : BinaryBicone X Y} (hb : b.IsBilimit) : (F.mapBinaryBicone b).IsBilimit :=
  PreservesBinaryBiproduct.preserves hb

/-- A functor `F` preserves binary biproducts if it preserves the binary biproduct of `X` and `Y`
    for all `X` and `Y`. -/
class PreservesBinaryBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] where
  preserves : ∀ {X Y : C}, PreservesBinaryBiproduct X Y F := by infer_instance

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preservesBinaryBiproductOfPreservesBiproduct (F : C ⥤ D) [PreservesZeroMorphisms F] (X Y : C)
    [PreservesBiproduct (pairFunction X Y) F] :
    PreservesBinaryBiproduct X Y
      F where preserves b hb :=
    { IsLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagram_iso_pair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).IsLimit) <|
          Cones.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩
            tidy,
      IsColimit :=
        IsColimit.ofIsoColimit
            ((IsColimit.precomposeInvEquiv (diagram_iso_pair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).IsColimit) <|
          Cocones.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩
            tidy }

/-- A functor that preserves biproducts of a pair preserves binary biproducts. -/
def preservesBinaryBiproductsOfPreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproductsOfShape WalkingPair F] :
    PreservesBinaryBiproducts F where preserves X Y := preservesBinaryBiproductOfPreservesBiproduct F X Y

attribute [instance] preserves_binary_biproducts.preserves

end Limits

open CategoryTheory.Limits

namespace Functor

section Bicone

variable {J : Type w₁} (F : C ⥤ D) (f : J → C) [HasBiproduct f]

section

variable [HasBiproduct (F.obj ∘ f)]

/-- As for products, any functor between categories with biproducts gives rise to a morphism
    `F.obj (⨁ f) ⟶ ⨁ (F.obj ∘ f)`. -/
def biproductComparison : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f :=
  biproduct.lift fun j => F.map (biproduct.π f j)

@[simp, reassoc]
theorem biproduct_comparison_π (j : J) : biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j) :=
  biproduct.lift_π _ _

/-- As for coproducts, any functor between categories with biproducts gives rise to a morphism
    `⨁ (F.obj ∘ f) ⟶ F.obj (⨁ f)` -/
def biproductComparison' : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f) :=
  biproduct.desc fun j => F.map (biproduct.ι f j)

@[simp, reassoc]
theorem ι_biproduct_comparison' (j : J) : biproduct.ι _ j ≫ biproductComparison' F f = F.map (biproduct.ι f j) :=
  biproduct.ι_desc _ _

variable [PreservesZeroMorphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
    the biproduct, see `preserves_biproduct_of_mono_biproduct_comparison`.  -/
@[simp, reassoc]
theorem biproduct_comparison'_comp_biproduct_comparison :
    biproductComparison' F f ≫ biproductComparison F f = 𝟙 (⨁ F.obj ∘ f) := by
  classical
  ext
  simp [biproduct.ι_π, ← functor.map_comp, eq_to_hom_map]

/-- `biproduct_comparison F f` is a split epimorphism. -/
@[simps]
def splitEpiBiproductComparison : SplitEpi (biproductComparison F f) :=
  ⟨biproductComparison' F f⟩

instance : IsSplitEpi (biproductComparison F f) :=
  IsSplitEpi.mk' (splitEpiBiproductComparison F f)

/-- `biproduct_comparison' F f` is a split monomorphism. -/
@[simps]
def splitMonoBiproductComparison' : SplitMono (biproductComparison' F f) :=
  ⟨biproductComparison F f⟩

instance : IsSplitMono (biproductComparison' F f) :=
  IsSplitMono.mk' (splitMonoBiproductComparison' F f)

end

variable [PreservesZeroMorphisms F] [PreservesBiproduct f F]

instance has_biproduct_of_preserves : HasBiproduct (F.obj ∘ f) :=
  HasBiproduct.mk
    { Bicone := F.mapBicone (Biproduct.bicone f), IsBilimit := PreservesBiproduct.preserves (Biproduct.isBilimit _) }

/-- If `F` preserves a biproduct, we get a definitionally nice isomorphism
    `F.obj (⨁ f) ≅ ⨁ (F.obj ∘ f)`. -/
@[simp]
def mapBiproduct : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f :=
  biproduct.uniqueUpToIso _ (PreservesBiproduct.preserves (Biproduct.isBilimit _))

theorem map_biproduct_hom : (mapBiproduct F f).Hom = biproduct.lift fun j => F.map (biproduct.π f j) :=
  rfl

theorem map_biproduct_inv : (mapBiproduct F f).inv = biproduct.desc fun j => F.map (biproduct.ι f j) :=
  rfl

end Bicone

variable (F : C ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]

section

variable [HasBinaryBiproduct (F.obj X) (F.obj Y)]

/-- As for products, any functor between categories with binary biproducts gives rise to a
    morphism `F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y`. -/
def biprodComparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y :=
  biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[simp, reassoc]
theorem biprod_comparison_fst : biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst :=
  biprod.lift_fst _ _

@[simp, reassoc]
theorem biprod_comparison_snd : biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd :=
  biprod.lift_snd _ _

/-- As for coproducts, any functor between categories with binary biproducts gives rise to a
    morphism `F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)`. -/
def biprodComparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y) :=
  biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[simp, reassoc]
theorem inl_biprod_comparison' : biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl :=
  biprod.inl_desc _ _

@[simp, reassoc]
theorem inr_biprod_comparison' : biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr :=
  biprod.inr_desc _ _

variable [PreservesZeroMorphisms F]

/-- The composition in the opposite direction is equal to the identity if and only if `F` preserves
    the biproduct, see `preserves_binary_biproduct_of_mono_biprod_comparison`. -/
@[simp, reassoc]
theorem biprod_comparison'_comp_biprod_comparison :
    biprodComparison' F X Y ≫ biprodComparison F X Y = 𝟙 (F.obj X ⊞ F.obj Y) := by ext <;> simp [← functor.map_comp]

/-- `biprod_comparison F X Y` is a split epi. -/
@[simps]
def splitEpiBiprodComparison : SplitEpi (biprodComparison F X Y) :=
  ⟨biprodComparison' F X Y⟩

instance : IsSplitEpi (biprodComparison F X Y) :=
  IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

/-- `biprod_comparison' F X Y` is a split mono. -/
@[simps]
def splitMonoBiprodComparison' : SplitMono (biprodComparison' F X Y) :=
  ⟨biprodComparison F X Y⟩

instance : IsSplitMono (biprodComparison' F X Y) :=
  IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

end

variable [PreservesZeroMorphisms F] [PreservesBinaryBiproduct X Y F]

instance has_binary_biproduct_of_preserves : HasBinaryBiproduct (F.obj X) (F.obj Y) :=
  HasBinaryBiproduct.mk
    { Bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y),
      IsBilimit := PreservesBinaryBiproduct.preserves (BinaryBiproduct.isBilimit _ _) }

/-- If `F` preserves a binary biproduct, we get a definitionally nice isomorphism
    `F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y`. -/
@[simp]
def mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  biprod.uniqueUpToIso _ _ (PreservesBinaryBiproduct.preserves (BinaryBiproduct.isBilimit _ _))

theorem map_biprod_hom : (mapBiprod F X Y).Hom = biprod.lift (F.map biprod.fst) (F.map biprod.snd) :=
  rfl

theorem map_biprod_inv : (mapBiprod F X Y).inv = biprod.desc (F.map biprod.inl) (F.map biprod.inr) :=
  rfl

end Functor

namespace Limits

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁} (f : J → C) [HasBiproduct f] [PreservesBiproduct f F] {W : C}

theorem biproduct.map_lift_map_biprod (g : ∀ j, W ⟶ f j) :
    F.map (biproduct.lift g) ≫ (F.mapBiproduct f).Hom = biproduct.lift fun j => F.map (g j) := by
  ext
  simp [← F.map_comp]

theorem biproduct.map_biproduct_inv_map_desc (g : ∀ j, f j ⟶ W) :
    (F.mapBiproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc fun j => F.map (g j) := by
  ext
  simp [← F.map_comp]

theorem biproduct.map_biproduct_hom_desc (g : ∀ j, f j ⟶ W) :
    ((F.mapBiproduct f).Hom ≫ biproduct.desc fun j => F.map (g j)) = F.map (biproduct.desc g) := by
  rw [← biproduct.map_biproduct_inv_map_desc, iso.hom_inv_id_assoc]

end Bicone

section BinaryBicone

variable (X Y : C) [HasBinaryBiproduct X Y] [PreservesBinaryBiproduct X Y F] {W : C}

theorem biprod.map_lift_map_biprod (f : W ⟶ X) (g : W ⟶ Y) :
    F.map (biprod.lift f g) ≫ (F.mapBiprod X Y).Hom = biprod.lift (F.map f) (F.map g) := by ext <;> simp [← F.map_comp]

theorem biprod.lift_map_biprod (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift (F.map f) (F.map g) ≫ (F.mapBiprod X Y).inv = F.map (biprod.lift f g) := by
  rw [← biprod.map_lift_map_biprod, category.assoc, iso.hom_inv_id, category.comp_id]

theorem biprod.map_biprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) := by ext <;> simp [← F.map_comp]

theorem biprod.map_biprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).Hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) := by
  rw [← biprod.map_biprod_inv_map_desc, iso.hom_inv_id_assoc]

end BinaryBicone

end Limits

end HasZeroMorphisms

end CategoryTheory

