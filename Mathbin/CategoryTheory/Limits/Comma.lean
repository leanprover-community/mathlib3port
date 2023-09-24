/-
Copyright (c) 2021 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import CategoryTheory.Arrow
import CategoryTheory.Limits.Constructions.EpiMono
import CategoryTheory.Limits.Creates
import CategoryTheory.Limits.Unit
import CategoryTheory.StructuredArrow

#align_import category_theory.limits.comma from "leanprover-community/mathlib"@"69c6a5a12d8a2b159f20933e60115a4f2de62b58"

/-!
# Limits and colimits in comma categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We build limits in the comma category `comma L R` provided that the two source categories have
limits and `R` preserves them.
This is used to construct limits in the arrow category, structured arrow category and under
category, and show that the appropriate forgetful functors create limits.

The duals of all the above are also given.
-/


namespace CategoryTheory

open Category Limits

universe w' w v u₁ u₂ u₃

variable {J : Type w} [Category.{w'} J]

variable {A : Type u₁} [Category.{v} A]

variable {B : Type u₂} [Category.{v} B]

variable {T : Type u₃} [Category.{v} T]

namespace Comma

variable {L : A ⥤ T} {R : B ⥤ T}

variable (F : J ⥤ Comma L R)

#print CategoryTheory.Comma.limitAuxiliaryCone /-
/-- (Implementation). An auxiliary cone which is useful in order to construct limits
in the comma category. -/
@[simps]
def limitAuxiliaryCone (c₁ : Cone (F ⋙ fst L R)) : Cone ((F ⋙ snd L R) ⋙ R) :=
  (Cones.postcompose (whiskerLeft F (Comma.natTrans L R) : _)).obj (L.mapCone c₁)
#align category_theory.comma.limit_auxiliary_cone CategoryTheory.Comma.limitAuxiliaryCone
-/

#print CategoryTheory.Comma.coneOfPreserves /-
/-- If `R` preserves the appropriate limit, then given a cone for `F ⋙ fst L R : J ⥤ L` and a
limit cone for `F ⋙ snd L R : J ⥤ R` we can build a cone for `F` which will turn out to be a limit
cone.
-/
@[simps]
def coneOfPreserves [PreservesLimit (F ⋙ snd L R) R] (c₁ : Cone (F ⋙ fst L R))
    {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) : Cone F
    where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      Hom := (isLimitOfPreserves R t₂).lift (limitAuxiliaryCone _ c₁) }
  π :=
    { app := fun j =>
        { left := c₁.π.app j
          right := c₂.π.app j
          w' := ((isLimitOfPreserves R t₂).fac (limitAuxiliaryCone F c₁) j).symm }
      naturality' := fun j₁ j₂ t => by ext <;> dsimp <;> simp [← c₁.w t, ← c₂.w t] }
#align category_theory.comma.cone_of_preserves CategoryTheory.Comma.coneOfPreserves
-/

#print CategoryTheory.Comma.coneOfPreservesIsLimit /-
/-- Provided that `R` preserves the appropriate limit, then the cone in `cone_of_preserves` is a
limit. -/
def coneOfPreservesIsLimit [PreservesLimit (F ⋙ snd L R) R] {c₁ : Cone (F ⋙ fst L R)}
    (t₁ : IsLimit c₁) {c₂ : Cone (F ⋙ snd L R)} (t₂ : IsLimit c₂) :
    IsLimit (coneOfPreserves F c₁ t₂)
    where
  lift s :=
    { left := t₁.lift ((fst L R).mapCone s)
      right := t₂.lift ((snd L R).mapCone s)
      w' :=
        (isLimitOfPreserves R t₂).hom_ext fun j =>
          by
          rw [cone_of_preserves_X_hom, assoc, assoc, (is_limit_of_preserves R t₂).fac,
            limit_auxiliary_cone_π_app, ← L.map_comp_assoc, t₁.fac, R.map_cone_π_app, ← R.map_comp,
            t₂.fac]
          exact (s.π.app j).w }
  uniq s m w :=
    CommaMorphism.ext _ _ (t₁.uniq ((fst L R).mapCone s) _ fun j => by simp [← w])
      (t₂.uniq ((snd L R).mapCone s) _ fun j => by simp [← w])
#align category_theory.comma.cone_of_preserves_is_limit CategoryTheory.Comma.coneOfPreservesIsLimit
-/

#print CategoryTheory.Comma.colimitAuxiliaryCocone /-
/-- (Implementation). An auxiliary cocone which is useful in order to construct colimits
in the comma category. -/
@[simps]
def colimitAuxiliaryCocone (c₂ : Cocone (F ⋙ snd L R)) : Cocone ((F ⋙ fst L R) ⋙ L) :=
  (Cocones.precompose (whiskerLeft F (Comma.natTrans L R) : _)).obj (R.mapCocone c₂)
#align category_theory.comma.colimit_auxiliary_cocone CategoryTheory.Comma.colimitAuxiliaryCocone
-/

#print CategoryTheory.Comma.coconeOfPreserves /-
/--
If `L` preserves the appropriate colimit, then given a colimit cocone for `F ⋙ fst L R : J ⥤ L` and
a cocone for `F ⋙ snd L R : J ⥤ R` we can build a cocone for `F` which will turn out to be a
colimit cocone.
-/
@[simps]
def coconeOfPreserves [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) (c₂ : Cocone (F ⋙ snd L R)) : Cocone F
    where
  pt :=
    { left := c₁.pt
      right := c₂.pt
      Hom := (isColimitOfPreserves L t₁).desc (colimitAuxiliaryCocone _ c₂) }
  ι :=
    { app := fun j =>
        { left := c₁.ι.app j
          right := c₂.ι.app j
          w' := (isColimitOfPreserves L t₁).fac (colimitAuxiliaryCocone _ c₂) j }
      naturality' := fun j₁ j₂ t => by ext <;> dsimp <;> simp [← c₁.w t, ← c₂.w t] }
#align category_theory.comma.cocone_of_preserves CategoryTheory.Comma.coconeOfPreserves
-/

#print CategoryTheory.Comma.coconeOfPreservesIsColimit /-
/-- Provided that `L` preserves the appropriate colimit, then the cocone in `cocone_of_preserves` is
a colimit. -/
def coconeOfPreservesIsColimit [PreservesColimit (F ⋙ fst L R) L] {c₁ : Cocone (F ⋙ fst L R)}
    (t₁ : IsColimit c₁) {c₂ : Cocone (F ⋙ snd L R)} (t₂ : IsColimit c₂) :
    IsColimit (coconeOfPreserves F t₁ c₂)
    where
  desc s :=
    { left := t₁.desc ((fst L R).mapCocone s)
      right := t₂.desc ((snd L R).mapCocone s)
      w' :=
        (isColimitOfPreserves L t₁).hom_ext fun j =>
          by
          rw [cocone_of_preserves_X_hom, (is_colimit_of_preserves L t₁).fac_assoc,
            colimit_auxiliary_cocone_ι_app, assoc, ← R.map_comp, t₂.fac, L.map_cocone_ι_app, ←
            L.map_comp_assoc, t₁.fac]
          exact (s.ι.app j).w }
  uniq s m w :=
    CommaMorphism.ext _ _ (t₁.uniq ((fst L R).mapCocone s) _ (by simp [← w]))
      (t₂.uniq ((snd L R).mapCocone s) _ (by simp [← w]))
#align category_theory.comma.cocone_of_preserves_is_colimit CategoryTheory.Comma.coconeOfPreservesIsColimit
-/

#print CategoryTheory.Comma.hasLimit /-
instance hasLimit (F : J ⥤ Comma L R) [HasLimit (F ⋙ fst L R)] [HasLimit (F ⋙ snd L R)]
    [PreservesLimit (F ⋙ snd L R) R] : HasLimit F :=
  HasLimit.mk ⟨_, coneOfPreservesIsLimit _ (limit.isLimit _) (limit.isLimit _)⟩
#align category_theory.comma.has_limit CategoryTheory.Comma.hasLimit
-/

#print CategoryTheory.Comma.hasLimitsOfShape /-
instance hasLimitsOfShape [HasLimitsOfShape J A] [HasLimitsOfShape J B]
    [PreservesLimitsOfShape J R] : HasLimitsOfShape J (Comma L R) where
#align category_theory.comma.has_limits_of_shape CategoryTheory.Comma.hasLimitsOfShape
-/

#print CategoryTheory.Comma.hasLimitsOfSize /-
instance hasLimitsOfSize [HasLimits A] [HasLimits B] [PreservesLimits R] : HasLimits (Comma L R) :=
  ⟨inferInstance⟩
#align category_theory.comma.has_limits CategoryTheory.Comma.hasLimitsOfSize
-/

#print CategoryTheory.Comma.hasColimit /-
instance hasColimit (F : J ⥤ Comma L R) [HasColimit (F ⋙ fst L R)] [HasColimit (F ⋙ snd L R)]
    [PreservesColimit (F ⋙ fst L R) L] : HasColimit F :=
  HasColimit.mk ⟨_, coconeOfPreservesIsColimit _ (colimit.isColimit _) (colimit.isColimit _)⟩
#align category_theory.comma.has_colimit CategoryTheory.Comma.hasColimit
-/

#print CategoryTheory.Comma.hasColimitsOfShape /-
instance hasColimitsOfShape [HasColimitsOfShape J A] [HasColimitsOfShape J B]
    [PreservesColimitsOfShape J L] : HasColimitsOfShape J (Comma L R) where
#align category_theory.comma.has_colimits_of_shape CategoryTheory.Comma.hasColimitsOfShape
-/

#print CategoryTheory.Comma.hasColimitsOfSize /-
instance hasColimitsOfSize [HasColimits A] [HasColimits B] [PreservesColimits L] :
    HasColimits (Comma L R) :=
  ⟨inferInstance⟩
#align category_theory.comma.has_colimits CategoryTheory.Comma.hasColimitsOfSize
-/

end Comma

namespace Arrow

#print CategoryTheory.Arrow.hasLimit /-
instance hasLimit (F : J ⥤ Arrow T) [i₁ : HasLimit (F ⋙ leftFunc)] [i₂ : HasLimit (F ⋙ rightFunc)] :
    HasLimit F :=
  @Comma.hasLimit _ _ _ _ _ i₁ i₂ _
#align category_theory.arrow.has_limit CategoryTheory.Arrow.hasLimit
-/

#print CategoryTheory.Arrow.hasLimitsOfShape /-
instance hasLimitsOfShape [HasLimitsOfShape J T] : HasLimitsOfShape J (Arrow T) where
#align category_theory.arrow.has_limits_of_shape CategoryTheory.Arrow.hasLimitsOfShape
-/

#print CategoryTheory.Arrow.hasLimits /-
instance hasLimits [HasLimits T] : HasLimits (Arrow T) :=
  ⟨inferInstance⟩
#align category_theory.arrow.has_limits CategoryTheory.Arrow.hasLimits
-/

#print CategoryTheory.Arrow.hasColimit /-
instance hasColimit (F : J ⥤ Arrow T) [i₁ : HasColimit (F ⋙ leftFunc)]
    [i₂ : HasColimit (F ⋙ rightFunc)] : HasColimit F :=
  @Comma.hasColimit _ _ _ _ _ i₁ i₂ _
#align category_theory.arrow.has_colimit CategoryTheory.Arrow.hasColimit
-/

#print CategoryTheory.Arrow.hasColimitsOfShape /-
instance hasColimitsOfShape [HasColimitsOfShape J T] : HasColimitsOfShape J (Arrow T) where
#align category_theory.arrow.has_colimits_of_shape CategoryTheory.Arrow.hasColimitsOfShape
-/

#print CategoryTheory.Arrow.hasColimits /-
instance hasColimits [HasColimits T] : HasColimits (Arrow T) :=
  ⟨inferInstance⟩
#align category_theory.arrow.has_colimits CategoryTheory.Arrow.hasColimits
-/

end Arrow

namespace StructuredArrow

variable {X : T} {G : A ⥤ T} (F : J ⥤ StructuredArrow X G)

#print CategoryTheory.StructuredArrow.hasLimit /-
instance hasLimit [i₁ : HasLimit (F ⋙ proj X G)] [i₂ : PreservesLimit (F ⋙ proj X G) G] :
    HasLimit F :=
  @Comma.hasLimit _ _ _ _ _ _ i₁ i₂
#align category_theory.structured_arrow.has_limit CategoryTheory.StructuredArrow.hasLimit
-/

#print CategoryTheory.StructuredArrow.hasLimitsOfShape /-
instance hasLimitsOfShape [HasLimitsOfShape J A] [PreservesLimitsOfShape J G] :
    HasLimitsOfShape J (StructuredArrow X G) where
#align category_theory.structured_arrow.has_limits_of_shape CategoryTheory.StructuredArrow.hasLimitsOfShape
-/

#print CategoryTheory.StructuredArrow.hasLimitsOfSize /-
instance hasLimitsOfSize [HasLimits A] [PreservesLimits G] : HasLimits (StructuredArrow X G) :=
  ⟨inferInstance⟩
#align category_theory.structured_arrow.has_limits CategoryTheory.StructuredArrow.hasLimitsOfSize
-/

#print CategoryTheory.StructuredArrow.createsLimit /-
noncomputable instance createsLimit [i : PreservesLimit (F ⋙ proj X G) G] :
    CreatesLimit F (proj X G) :=
  createsLimitOfReflectsIso fun c t =>
    { liftedCone := @Comma.coneOfPreserves _ _ _ _ _ i punitCone t
      makesLimit := Comma.coneOfPreservesIsLimit _ punitConeIsLimit _
      validLift := Cones.ext (Iso.refl _) fun j => (id_comp _).symm }
#align category_theory.structured_arrow.creates_limit CategoryTheory.StructuredArrow.createsLimit
-/

#print CategoryTheory.StructuredArrow.createsLimitsOfShape /-
noncomputable instance createsLimitsOfShape [PreservesLimitsOfShape J G] :
    CreatesLimitsOfShape J (proj X G) where
#align category_theory.structured_arrow.creates_limits_of_shape CategoryTheory.StructuredArrow.createsLimitsOfShape
-/

#print CategoryTheory.StructuredArrow.createsLimitsOfSize /-
noncomputable instance createsLimitsOfSize [PreservesLimits G] : CreatesLimits (proj X G : _) :=
  ⟨⟩
#align category_theory.structured_arrow.creates_limits CategoryTheory.StructuredArrow.createsLimitsOfSize
-/

#print CategoryTheory.StructuredArrow.mono_right_of_mono /-
instance mono_right_of_mono [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) [Mono f] : Mono f.right :=
  show Mono ((proj X G).map f) from inferInstance
#align category_theory.structured_arrow.mono_right_of_mono CategoryTheory.StructuredArrow.mono_right_of_mono
-/

#print CategoryTheory.StructuredArrow.mono_iff_mono_right /-
theorem mono_iff_mono_right [HasPullbacks A] [PreservesLimitsOfShape WalkingCospan G]
    {Y Z : StructuredArrow X G} (f : Y ⟶ Z) : Mono f ↔ Mono f.right :=
  ⟨fun h => inferInstance, fun h => mono_of_mono_right f⟩
#align category_theory.structured_arrow.mono_iff_mono_right CategoryTheory.StructuredArrow.mono_iff_mono_right
-/

end StructuredArrow

namespace CostructuredArrow

variable {G : A ⥤ T} {X : T} (F : J ⥤ CostructuredArrow G X)

#print CategoryTheory.CostructuredArrow.hasColimit /-
instance hasColimit [i₁ : HasColimit (F ⋙ proj G X)] [i₂ : PreservesColimit (F ⋙ proj G X) G] :
    HasColimit F :=
  @Comma.hasColimit _ _ _ _ _ i₁ _ i₂
#align category_theory.costructured_arrow.has_colimit CategoryTheory.CostructuredArrow.hasColimit
-/

#print CategoryTheory.CostructuredArrow.hasColimitsOfShape /-
instance hasColimitsOfShape [HasColimitsOfShape J A] [PreservesColimitsOfShape J G] :
    HasColimitsOfShape J (CostructuredArrow G X) where
#align category_theory.costructured_arrow.has_colimits_of_shape CategoryTheory.CostructuredArrow.hasColimitsOfShape
-/

#print CategoryTheory.CostructuredArrow.hasColimitsOfSize /-
instance hasColimitsOfSize [HasColimits A] [PreservesColimits G] :
    HasColimits (CostructuredArrow G X) :=
  ⟨inferInstance⟩
#align category_theory.costructured_arrow.has_colimits CategoryTheory.CostructuredArrow.hasColimitsOfSize
-/

#print CategoryTheory.CostructuredArrow.createsColimit /-
noncomputable instance createsColimit [i : PreservesColimit (F ⋙ proj G X) G] :
    CreatesColimit F (proj G X) :=
  createsColimitOfReflectsIso fun c t =>
    { liftedCocone := @Comma.coconeOfPreserves _ _ _ _ _ i t punitCocone
      makesColimit := Comma.coconeOfPreservesIsColimit _ _ punitCoconeIsColimit
      validLift := Cocones.ext (Iso.refl _) fun j => comp_id _ }
#align category_theory.costructured_arrow.creates_colimit CategoryTheory.CostructuredArrow.createsColimit
-/

#print CategoryTheory.CostructuredArrow.createsColimitsOfShape /-
noncomputable instance createsColimitsOfShape [PreservesColimitsOfShape J G] :
    CreatesColimitsOfShape J (proj G X) where
#align category_theory.costructured_arrow.creates_colimits_of_shape CategoryTheory.CostructuredArrow.createsColimitsOfShape
-/

#print CategoryTheory.CostructuredArrow.createsColimitsOfSize /-
noncomputable instance createsColimitsOfSize [PreservesColimits G] :
    CreatesColimits (proj G X : _) :=
  ⟨⟩
#align category_theory.costructured_arrow.creates_colimits CategoryTheory.CostructuredArrow.createsColimitsOfSize
-/

#print CategoryTheory.CostructuredArrow.epi_left_of_epi /-
instance epi_left_of_epi [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) [Epi f] : Epi f.left :=
  show Epi ((proj G X).map f) from inferInstance
#align category_theory.costructured_arrow.epi_left_of_epi CategoryTheory.CostructuredArrow.epi_left_of_epi
-/

#print CategoryTheory.CostructuredArrow.epi_iff_epi_left /-
theorem epi_iff_epi_left [HasPushouts A] [PreservesColimitsOfShape WalkingSpan G]
    {Y Z : CostructuredArrow G X} (f : Y ⟶ Z) : Epi f ↔ Epi f.left :=
  ⟨fun h => inferInstance, fun h => epi_of_epi_left f⟩
#align category_theory.costructured_arrow.epi_iff_epi_left CategoryTheory.CostructuredArrow.epi_iff_epi_left
-/

end CostructuredArrow

end CategoryTheory

