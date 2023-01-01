/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.locally_ringed_space.has_colimits
! leanprover-community/mathlib commit ffc3730d545623aedf5d5bd46a3153cbf41f6c2c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.LocallyRingedSpace
import Mathbin.Algebra.Category.RingCat.Constructions
import Mathbin.AlgebraicGeometry.OpenImmersion
import Mathbin.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-!
# Colimits of LocallyRingedSpace

We construct the explicit coproducts and coequalizers of `LocallyRingedSpace`.
It then follows that `LocallyRingedSpace` has all colimits, and
`forget_to_SheafedSpace` preserves them.

-/


namespace AlgebraicGeometry

universe v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace SheafedSpaceCat

variable {C : Type u} [Category.{v} C] [HasLimits C]

variable {J : Type v} [Category.{v} J] (F : J ⥤ SheafedSpaceCat C)

theorem is_colimit_exists_rep {c : Cocone F} (hc : IsColimit c) (x : c.x) :
    ∃ (i : J)(y : F.obj i), (c.ι.app i).base y = x :=
  Concrete.is_colimit_exists_rep (F ⋙ SheafedSpaceCat.forget _)
    (isColimitOfPreserves (SheafedSpaceCat.forget _) hc) x
#align
  algebraic_geometry.SheafedSpace.is_colimit_exists_rep AlgebraicGeometry.SheafedSpaceCat.is_colimit_exists_rep

theorem colimit_exists_rep (x : colimit F) : ∃ (i : J)(y : F.obj i), (colimit.ι F i).base y = x :=
  Concrete.is_colimit_exists_rep (F ⋙ SheafedSpaceCat.forget _)
    (isColimitOfPreserves (SheafedSpaceCat.forget _) (colimit.isColimit F)) x
#align
  algebraic_geometry.SheafedSpace.colimit_exists_rep AlgebraicGeometry.SheafedSpaceCat.colimit_exists_rep

instance {X Y : SheafedSpaceCat C} (f g : X ⟶ Y) : Epi (coequalizer.π f g).base :=
  by
  erw [←
    show _ = (coequalizer.π f g).base from
      ι_comp_coequalizer_comparison f g (SheafedSpace.forget C)]
  rw [← preserves_coequalizer.iso_hom]
  apply epi_comp

end SheafedSpaceCat

namespace LocallyRingedSpaceCat

section HasCoproducts

variable {ι : Type u} (F : Discrete ι ⥤ LocallyRingedSpace.{u})

/-- The explicit coproduct for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable def coproduct : LocallyRingedSpaceCat
    where
  toSheafedSpace := colimit (F ⋙ forget_to_SheafedSpace : _)
  LocalRing x :=
    by
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forget_to_SheafedSpace) x
    haveI : _root_.local_ring (((F ⋙ forget_to_SheafedSpace).obj i).toPresheafedSpace.stalk y) :=
      (F.obj i).LocalRing _
    exact
      (as_iso
              (PresheafedSpace.stalk_map (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _)
                y)).symm.commRingIsoToRingEquiv.LocalRing
#align
  algebraic_geometry.LocallyRingedSpace.coproduct AlgebraicGeometry.LocallyRingedSpaceCat.coproduct

/-- The explicit coproduct cofan for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable def coproductCofan : Cocone F
    where
  x := coproduct F
  ι :=
    { app := fun j => ⟨colimit.ι (F ⋙ forget_to_SheafedSpace) j, inferInstance⟩
      naturality' := fun j j' f => by
        cases j
        cases j'
        tidy }
#align
  algebraic_geometry.LocallyRingedSpace.coproduct_cofan AlgebraicGeometry.LocallyRingedSpaceCat.coproductCofan

/-- The explicit coproduct cofan constructed in `coproduct_cofan` is indeed a colimit. -/
noncomputable def coproductCofanIsColimit : IsColimit (coproductCofan F)
    where
  desc s :=
    ⟨colimit.desc (F ⋙ forget_to_SheafedSpace) (forgetToSheafedSpace.mapCocone s),
      by
      intro x
      obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forget_to_SheafedSpace) x
      have :=
        PresheafedSpace.stalk_map.comp (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _)
          (colimit.desc (F ⋙ forget_to_SheafedSpace) (forget_to_SheafedSpace.map_cocone s)) y
      rw [← is_iso.comp_inv_eq] at this
      erw [← this,
        PresheafedSpace.stalk_map.congr_hom _ _
          (colimit.ι_desc (forget_to_SheafedSpace.map_cocone s) i : _)]
      haveI :
        IsLocalRingHom
          (PresheafedSpace.stalk_map ((forget_to_SheafedSpace.map_cocone s).ι.app i) y) :=
        (s.ι.app i).2 y
      infer_instance⟩
  fac' s j := LocallyRingedSpaceCat.Hom.ext _ _ (colimit.ι_desc _ _)
  uniq' s f h :=
    LocallyRingedSpaceCat.Hom.ext _ _
      (IsColimit.uniq _ (forgetToSheafedSpace.mapCocone s) f.1 fun j =>
        congr_arg LocallyRingedSpaceCat.Hom.val (h j))
#align
  algebraic_geometry.LocallyRingedSpace.coproduct_cofan_is_colimit AlgebraicGeometry.LocallyRingedSpaceCat.coproductCofanIsColimit

instance : HasCoproducts.{u} LocallyRingedSpaceCat.{u} := fun ι =>
  ⟨fun F => ⟨⟨⟨_, coproductCofanIsColimit F⟩⟩⟩⟩

noncomputable instance (J : Type _) : PreservesColimitsOfShape (Discrete J) forgetToSheafedSpace :=
  ⟨fun G =>
    preservesColimitOfPreservesColimitCocone (coproductCofanIsColimit G)
      ((colimit.isColimit _).ofIsoColimit (Cocones.ext (Iso.refl _) fun j => Category.comp_id _))⟩

end HasCoproducts

section HasCoequalizer

variable {X Y : LocallyRingedSpaceCat.{v}} (f g : X ⟶ Y)

namespace HasCoequalizer

instance coequalizer_π_app_is_local_ring_hom
    (U : TopologicalSpace.Opens (coequalizer f.val g.val).carrier) :
    IsLocalRingHom ((coequalizer.π f.val g.val : _).c.app (op U)) :=
  by
  have := ι_comp_coequalizer_comparison f.1 g.1 SheafedSpace.forget_to_PresheafedSpace
  rw [← preserves_coequalizer.iso_hom] at this
  erw [SheafedSpace.congr_app this.symm (op U)]
  rw [PresheafedSpace.comp_c_app, ←
    PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π]
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.has_coequalizer.coequalizer_π_app_is_local_ring_hom AlgebraicGeometry.LocallyRingedSpaceCat.HasCoequalizer.coequalizer_π_app_is_local_ring_hom

/-!
We roughly follow the construction given in [MR0302656]. Given a pair `f, g : X ⟶ Y` of morphisms
of locally ringed spaces, we want to show that the stalk map of
`π = coequalizer.π f g` (as sheafed space homs) is a local ring hom. It then follows that
`coequalizer f g` is indeed a locally ringed space, and `coequalizer.π f g` is a morphism of
locally ringed space.

Given a germ `⟨U, s⟩` of `x : coequalizer f g` such that `π꙳ x : Y` is invertible, we ought to show
that `⟨U, s⟩` is invertible. That is, there exists an open set `U' ⊆ U` containing `x` such that the
restriction of `s` onto `U'` is invertible. This `U'` is given by `π '' V`, where `V` is the
basic open set of `π⋆x`.

Since `f ⁻¹' V = Y.basic_open (f ≫ π)꙳ x = Y.basic_open (g ≫ π)꙳ x = g ⁻¹' V`, we have
`π ⁻¹' (π '' V) = V` (as the underlying set map is merely the set-theoretic coequalizer).
This shows that `π '' V` is indeed open, and `s` is invertible on `π '' V` as the components of `π꙳`
are local ring homs.
-/


variable (U : Opens (coequalizer f.1 g.1).carrier)

variable (s : (coequalizer f.1 g.1).Presheaf.obj (op U))

/-- (Implementation). The basic open set of the section `π꙳ s`. -/
noncomputable def imageBasicOpen : Opens Y :=
  Y.toRingedSpace.basicOpen
    (show Y.Presheaf.obj (op (unop _)) from ((coequalizer.π f.1 g.1).c.app (op U)) s)
#align
  algebraic_geometry.LocallyRingedSpace.has_coequalizer.image_basic_open AlgebraicGeometry.LocallyRingedSpaceCat.HasCoequalizer.imageBasicOpen

theorem image_basic_open_image_preimage :
    (coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' (imageBasicOpen f g U s).1) =
      (imageBasicOpen f g U s).1 :=
  by
  fapply types.coequalizer_preimage_image_eq_of_preimage_eq f.1.base g.1.base
  · ext
    simp_rw [types_comp_apply, ← TopCat.comp_app, ← PresheafedSpace.comp_base]
    congr 2
    exact coequalizer.condition f.1 g.1
  · apply is_colimit_cofork_map_of_is_colimit (forget TopCat)
    apply is_colimit_cofork_map_of_is_colimit (SheafedSpace.forget _)
    exact coequalizer_is_coequalizer f.1 g.1
  · suffices
      (TopologicalSpace.Opens.map f.1.base).obj (image_basic_open f g U s) =
        (TopologicalSpace.Opens.map g.1.base).obj (image_basic_open f g U s)
      by injection this
    delta image_basic_open
    rw [preimage_basic_open f, preimage_basic_open g]
    dsimp only [functor.op, unop_op]
    rw [← comp_apply, ← SheafedSpace.comp_c_app', ← comp_apply, ← SheafedSpace.comp_c_app',
      SheafedSpace.congr_app (coequalizer.condition f.1 g.1), comp_apply]
    erw [X.to_RingedSpace.basic_open_res]
    apply inf_eq_right.mpr
    refine' (RingedSpace.basic_open_le _ _).trans _
    rw [coequalizer.condition f.1 g.1]
    exact fun _ h => h
#align
  algebraic_geometry.LocallyRingedSpace.has_coequalizer.image_basic_open_image_preimage AlgebraicGeometry.LocallyRingedSpaceCat.HasCoequalizer.image_basic_open_image_preimage

theorem image_basic_open_image_open :
    IsOpen ((coequalizer.π f.1 g.1).base '' (imageBasicOpen f g U s).1) :=
  by
  rw [←
    (TopCat.homeoOfIso
        (preserves_coequalizer.iso (SheafedSpace.forget _) f.1 g.1)).is_open_preimage,
    TopCat.coequalizer_is_open_iff, ← Set.preimage_comp]
  erw [← coe_comp]
  rw [preserves_coequalizer.iso_hom, ι_comp_coequalizer_comparison]
  dsimp only [SheafedSpace.forget]
  rw [image_basic_open_image_preimage]
  exact (image_basic_open f g U s).2
#align
  algebraic_geometry.LocallyRingedSpace.has_coequalizer.image_basic_open_image_open AlgebraicGeometry.LocallyRingedSpaceCat.HasCoequalizer.image_basic_open_image_open

instance coequalizer_π_stalk_is_local_ring_hom (x : Y) :
    IsLocalRingHom (PresheafedSpaceCat.stalkMap (coequalizer.π f.val g.val : _) x) :=
  by
  constructor
  rintro a ha
  rcases TopCat.Presheaf.germ_exist _ _ a with ⟨U, hU, s, rfl⟩
  erw [PresheafedSpace.stalk_map_germ_apply (coequalizer.π f.1 g.1 : _) U ⟨_, hU⟩] at ha
  let V := image_basic_open f g U s
  have hV : (coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' V.1) = V.1 :=
    image_basic_open_image_preimage f g U s
  have hV' :
    V = ⟨(coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' V.1), hV.symm ▸ V.2⟩ :=
    Subtype.eq hV.symm
  have V_open : IsOpen ((coequalizer.π f.val g.val).base '' V.val) :=
    image_basic_open_image_open f g U s
  have VleU :
    (⟨(coequalizer.π f.val g.val).base '' V.val, V_open⟩ : TopologicalSpace.Opens _) ≤ U :=
    set.image_subset_iff.mpr (Y.to_RingedSpace.basic_open_le _)
  have hxV : x ∈ V := ⟨⟨_, hU⟩, ha, rfl⟩
  erw [←
    (coequalizer f.val g.val).Presheaf.germ_res_apply (hom_of_le VleU)
      ⟨_, @Set.mem_image_of_mem _ _ (coequalizer.π f.val g.val).base x V.1 hxV⟩ s]
  apply RingHom.isUnit_map
  rw [← is_unit_map_iff ((coequalizer.π f.val g.val : _).c.app _), ← comp_apply,
    nat_trans.naturality, comp_apply, TopCat.Presheaf.pushforward_obj_map, ←
    is_unit_map_iff (Y.presheaf.map (eq_to_hom hV').op), ← comp_apply, ← functor.map_comp]
  convert
    @RingedSpace.is_unit_res_basic_open Y.to_RingedSpace (unop _)
      (((coequalizer.π f.val g.val).c.app (op U)) s)
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.has_coequalizer.coequalizer_π_stalk_is_local_ring_hom AlgebraicGeometry.LocallyRingedSpaceCat.HasCoequalizer.coequalizer_π_stalk_is_local_ring_hom

end HasCoequalizer

/-- The coequalizer of two locally ringed space in the category of sheafed spaces is a locally
ringed space. -/
noncomputable def coequalizer : LocallyRingedSpaceCat
    where
  toSheafedSpace := coequalizer f.1 g.1
  LocalRing x :=
    by
    obtain ⟨y, rfl⟩ :=
      (TopCat.epi_iff_surjective (coequalizer.π f.val g.val).base).mp inferInstance x
    exact (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) y).domain_local_ring
#align
  algebraic_geometry.LocallyRingedSpace.coequalizer AlgebraicGeometry.LocallyRingedSpaceCat.coequalizer

/-- The explicit coequalizer cofork of locally ringed spaces. -/
noncomputable def coequalizerCofork : Cofork f g :=
  @Cofork.ofπ _ _ _ _ f g (coequalizer f g) ⟨coequalizer.π f.1 g.1, inferInstance⟩
    (LocallyRingedSpaceCat.Hom.ext _ _ (coequalizer.condition f.1 g.1))
#align
  algebraic_geometry.LocallyRingedSpace.coequalizer_cofork AlgebraicGeometry.LocallyRingedSpaceCat.coequalizerCofork

theorem is_local_ring_hom_stalk_map_congr {X Y : RingedSpaceCat} (f g : X ⟶ Y) (H : f = g) (x)
    (h : IsLocalRingHom (PresheafedSpaceCat.stalkMap f x)) :
    IsLocalRingHom (PresheafedSpaceCat.stalkMap g x) :=
  by
  rw [PresheafedSpace.stalk_map.congr_hom _ _ H.symm x]
  infer_instance
#align
  algebraic_geometry.LocallyRingedSpace.is_local_ring_hom_stalk_map_congr AlgebraicGeometry.LocallyRingedSpaceCat.is_local_ring_hom_stalk_map_congr

/-- The cofork constructed in `coequalizer_cofork` is indeed a colimit cocone. -/
noncomputable def coequalizerCoforkIsColimit : IsColimit (coequalizerCofork f g) :=
  by
  apply cofork.is_colimit.mk'
  intro s
  have e : f.val ≫ s.π.val = g.val ≫ s.π.val := by injection s.condition
  use coequalizer.desc s.π.1 e
  · intro x
    rcases(TopCat.epi_iff_surjective (coequalizer.π f.val g.val).base).mp inferInstance x with
      ⟨y, rfl⟩
    apply is_local_ring_hom_of_comp _ (PresheafedSpace.stalk_map (coequalizer_cofork f g).π.1 _)
    change IsLocalRingHom (_ ≫ PresheafedSpace.stalk_map (coequalizer_cofork f g).π.val y)
    erw [← PresheafedSpace.stalk_map.comp]
    apply is_local_ring_hom_stalk_map_congr _ _ (coequalizer.π_desc s.π.1 e).symm y
    infer_instance
  constructor
  · exact LocallyRingedSpace.hom.ext _ _ (coequalizer.π_desc _ _)
  intro m h
  replace h : (coequalizer_cofork f g).π.1 ≫ m.1 = s.π.1 :=
    by
    rw [← h]
    rfl
  apply LocallyRingedSpace.hom.ext
  apply (colimit.is_colimit (parallel_pair f.1 g.1)).uniq (cofork.of_π s.π.1 e) m.1
  rintro ⟨⟩
  · rw [← (colimit.cocone (parallel_pair f.val g.val)).w walking_parallel_pair_hom.left,
      category.assoc]
    change _ ≫ _ ≫ _ = _ ≫ _
    congr
    exact h
  · exact h
#align
  algebraic_geometry.LocallyRingedSpace.coequalizer_cofork_is_colimit AlgebraicGeometry.LocallyRingedSpaceCat.coequalizerCoforkIsColimit

instance : HasCoequalizer f g :=
  ⟨⟨⟨_, coequalizerCoforkIsColimit f g⟩⟩⟩

instance : HasCoequalizers LocallyRingedSpaceCat :=
  has_coequalizers_of_has_colimit_parallel_pair _

noncomputable instance preservesCoequalizer :
    PreservesColimitsOfShape WalkingParallelPair forgetToSheafedSpace.{v} :=
  ⟨fun F => by
    apply preserves_colimit_of_iso_diagram _ (diagram_iso_parallel_pair F).symm
    apply preserves_colimit_of_preserves_colimit_cocone (coequalizer_cofork_is_colimit _ _)
    apply (is_colimit_map_cocone_cofork_equiv _ _).symm _
    dsimp only [forget_to_SheafedSpace]
    exact coequalizer_is_coequalizer _ _⟩
#align
  algebraic_geometry.LocallyRingedSpace.preserves_coequalizer AlgebraicGeometry.LocallyRingedSpaceCat.preservesCoequalizer

end HasCoequalizer

instance : HasColimits LocallyRingedSpaceCat :=
  has_colimits_of_has_coequalizers_and_coproducts

noncomputable instance : PreservesColimits LocallyRingedSpaceCat.forgetToSheafedSpace :=
  preservesColimitsOfPreservesCoequalizersAndCoproducts _

end LocallyRingedSpaceCat

end AlgebraicGeometry

