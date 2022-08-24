/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Andrew Yang
-/
import Mathbin.CategoryTheory.Limits.Shapes.Equalizers
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Constructing equalizers from pullbacks and binary products.

If a category has pullbacks and binary products, then it has equalizers.

TODO: generalize universe
-/


noncomputable section

universe v v' u u'

open CategoryTheory CategoryTheory.Category

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable {D : Type u'} [Category.{v'} D] (G : C ⥤ D)

-- We hide the "implementation details" inside a namespace
namespace HasEqualizersOfHasPullbacksAndBinaryProducts

variable [HasBinaryProducts C] [HasPullbacks C]

/-- Define the equalizing object -/
@[reducible]
def constructEqualizer (F : walking_parallel_pair ⥤ C) : C :=
  pullback (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.left)) (prod.lift (𝟙 _) (F.map WalkingParallelPairHom.right))

/-- Define the equalizing morphism -/
abbrev pullbackFst (F : walking_parallel_pair ⥤ C) : constructEqualizer F ⟶ F.obj WalkingParallelPair.zero :=
  pullback.fst

theorem pullback_fst_eq_pullback_snd (F : walking_parallel_pair ⥤ C) : pullbackFst F = pullback.snd := by
  convert pullback.condition =≫ limits.prod.fst <;> simp

/-- Define the equalizing cone -/
@[reducible]
def equalizerCone (F : walking_parallel_pair ⥤ C) : Cone F :=
  Cone.ofFork
    (Fork.ofι (pullbackFst F)
      (by
        conv_rhs => rw [pullback_fst_eq_pullback_snd]
        convert pullback.condition =≫ limits.prod.snd using 1 <;> simp ))

/-- Show the equalizing cone is a limit -/
def equalizerConeIsLimit (F : walking_parallel_pair ⥤ C) : IsLimit (equalizerCone F) where
  lift := by
    intro c
    apply pullback.lift (c.π.app _) (c.π.app _)
    apply limit.hom_ext
    rintro (_ | _) <;> simp
  fac' := by
    rintro c (_ | _) <;> simp
  uniq' := by
    intro c _ J
    have J0 := J walking_parallel_pair.zero
    simp at J0
    apply pullback.hom_ext
    · rwa [limit.lift_π]
      
    · erw [limit.lift_π, ← J0, pullback_fst_eq_pullback_snd]
      

end HasEqualizersOfHasPullbacksAndBinaryProducts

open HasEqualizersOfHasPullbacksAndBinaryProducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/-- Any category with pullbacks and binary products, has equalizers. -/
theorem has_equalizers_of_has_pullbacks_and_binary_products [HasBinaryProducts C] [HasPullbacks C] : HasEqualizers C :=
  { HasLimit := fun F => HasLimit.mk { Cone := equalizerCone F, IsLimit := equalizerConeIsLimit F } }

attribute [local instance] has_pullback_of_preserves_pullback

/-- A functor that preserves pullbacks and binary products also presrves equalizers. -/
def preservesEqualizersOfPreservesPullbacksAndBinaryProducts [HasBinaryProducts C] [HasPullbacks C]
    [PreservesLimitsOfShape (Discrete WalkingPair) G] [PreservesLimitsOfShape WalkingCospan G] :
    PreservesLimitsOfShape WalkingParallelPair G :=
  ⟨fun K =>
    preservesLimitOfPreservesLimitCone (equalizerConeIsLimit K) <|
      { lift := fun c => by
          refine' pullback.lift _ _ _ ≫ (@preserves_pullback.iso _ _ _ _ _ _ _ _).inv
          · exact c.π.app walking_parallel_pair.zero
            
          · exact c.π.app walking_parallel_pair.zero
            
          apply (map_is_limit_of_preserves_of_is_limit G _ _ (prod_is_prod _ _)).hom_ext
          swap
          infer_instance
          rintro (_ | _)
          · simp only [category.assoc, ← G.map_comp, prod.lift_fst, binary_fan.π_app_left, binary_fan.mk_fst]
            
          · simp only [binary_fan.π_app_right, binary_fan.mk_snd, category.assoc, ← G.map_comp, prod.lift_snd]
            exact
              (c.π.naturality walking_parallel_pair_hom.left).symm.trans
                (c.π.naturality walking_parallel_pair_hom.right)
            ,
        fac' := fun c j => by
          rcases j with (_ | _) <;>
            simp only [category.comp_id, preserves_pullback.iso_inv_fst, cone.of_fork_π, G.map_comp,
              preserves_pullback.iso_inv_fst_assoc, functor.map_cone_π_app, eq_to_hom_refl, category.assoc,
              fork.of_ι_π_app, pullback.lift_fst, pullback.lift_fst_assoc]
          exact (c.π.naturality walking_parallel_pair_hom.left).symm.trans (category.id_comp _),
        uniq' := fun s m h => by
          rw [iso.eq_comp_inv]
          have := h walking_parallel_pair.zero
          dsimp' [equalizer_cone]  at this
          ext <;>
            simp only [preserves_pullback.iso_hom_snd, category.assoc, preserves_pullback.iso_hom_fst,
              pullback.lift_fst, pullback.lift_snd, category.comp_id, ← pullback_fst_eq_pullback_snd, ← this] }⟩

-- We hide the "implementation details" inside a namespace
namespace HasCoequalizersOfHasPushoutsAndBinaryCoproducts

variable [HasBinaryCoproducts C] [HasPushouts C]

/-- Define the equalizing object -/
@[reducible]
def constructCoequalizer (F : walking_parallel_pair ⥤ C) : C :=
  pushout (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.left))
    (coprod.desc (𝟙 _) (F.map WalkingParallelPairHom.right))

/-- Define the equalizing morphism -/
abbrev pushoutInl (F : walking_parallel_pair ⥤ C) : F.obj WalkingParallelPair.one ⟶ constructCoequalizer F :=
  pushout.inl

theorem pushout_inl_eq_pushout_inr (F : walking_parallel_pair ⥤ C) : pushoutInl F = pushout.inr := by
  convert limits.coprod.inl ≫= pushout.condition <;> simp

/-- Define the equalizing cocone -/
@[reducible]
def coequalizerCocone (F : walking_parallel_pair ⥤ C) : Cocone F :=
  Cocone.ofCofork
    (Cofork.ofπ (pushoutInl F)
      (by
        conv_rhs => rw [pushout_inl_eq_pushout_inr]
        convert limits.coprod.inr ≫= pushout.condition using 1 <;> simp ))

/-- Show the equalizing cocone is a colimit -/
def coequalizerCoconeIsColimit (F : walking_parallel_pair ⥤ C) : IsColimit (coequalizerCocone F) where
  desc := by
    intro c
    apply pushout.desc (c.ι.app _) (c.ι.app _)
    apply colimit.hom_ext
    rintro (_ | _) <;> simp
  fac' := by
    rintro c (_ | _) <;> simp
  uniq' := by
    intro c _ J
    have J1 : pushout_inl F ≫ m = c.ι.app walking_parallel_pair.one := by
      simpa using J walking_parallel_pair.one
    apply pushout.hom_ext
    · rw [colimit.ι_desc]
      exact J1
      
    · rw [colimit.ι_desc, ← pushout_inl_eq_pushout_inr]
      exact J1
      

end HasCoequalizersOfHasPushoutsAndBinaryCoproducts

open HasCoequalizersOfHasPushoutsAndBinaryCoproducts

-- This is not an instance, as it is not always how one wants to construct equalizers!
/-- Any category with pullbacks and binary products, has equalizers. -/
theorem has_coequalizers_of_has_pushouts_and_binary_coproducts [HasBinaryCoproducts C] [HasPushouts C] :
    HasCoequalizers C :=
  { HasColimit := fun F => HasColimit.mk { Cocone := coequalizerCocone F, IsColimit := coequalizerCoconeIsColimit F } }

attribute [local instance] has_pushout_of_preserves_pushout

/-- A functor that preserves pushouts and binary coproducts also presrves coequalizers. -/
def preservesCoequalizersOfPreservesPushoutsAndBinaryCoproducts [HasBinaryCoproducts C] [HasPushouts C]
    [PreservesColimitsOfShape (Discrete WalkingPair) G] [PreservesColimitsOfShape WalkingSpan G] :
    PreservesColimitsOfShape WalkingParallelPair G :=
  ⟨fun K =>
    preservesColimitOfPreservesColimitCocone (coequalizerCoconeIsColimit K) <|
      { desc := fun c => by
          refine' (@preserves_pushout.iso _ _ _ _ _ _ _ _).inv ≫ pushout.desc _ _ _
          · exact c.ι.app walking_parallel_pair.one
            
          · exact c.ι.app walking_parallel_pair.one
            
          apply (map_is_colimit_of_preserves_of_is_colimit G _ _ (coprod_is_coprod _ _)).hom_ext
          swap
          infer_instance
          rintro (_ | _)
          · simp only [binary_cofan.ι_app_left, binary_cofan.mk_inl, category.assoc, ← G.map_comp_assoc,
              coprod.inl_desc]
            
          · simp only [binary_cofan.ι_app_right, binary_cofan.mk_inr, category.assoc, ← G.map_comp_assoc,
              coprod.inr_desc]
            exact
              (c.ι.naturality walking_parallel_pair_hom.left).trans
                (c.ι.naturality walking_parallel_pair_hom.right).symm
            ,
        fac' := fun c j => by
          rcases j with (_ | _) <;>
            simp only [functor.map_cocone_ι_app, cocone.of_cofork_ι, category.id_comp, eq_to_hom_refl, category.assoc,
              functor.map_comp, cofork.of_π_ι_app, pushout.inl_desc, preserves_pushout.inl_iso_inv_assoc]
          exact (c.ι.naturality walking_parallel_pair_hom.left).trans (category.comp_id _),
        uniq' := fun s m h => by
          rw [iso.eq_inv_comp]
          have := h walking_parallel_pair.one
          dsimp' [coequalizer_cocone]  at this
          ext <;>
            simp only [preserves_pushout.inl_iso_hom_assoc, category.id_comp, pushout.inl_desc, pushout.inr_desc,
              preserves_pushout.inr_iso_hom_assoc, ← pushout_inl_eq_pushout_inr, ← this] }⟩

end CategoryTheory.Limits

