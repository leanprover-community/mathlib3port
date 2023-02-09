/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.open_immersion
! leanprover-community/mathlib commit 0ebfdb71919ac6ca5d7fbc61a082fa2519556818
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.AlgebraicGeometry.PresheafedSpace.HasColimits
import Mathbin.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathbin.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathbin.Topology.Sheaves.Functors
import Mathbin.AlgebraicGeometry.Scheme
import Mathbin.CategoryTheory.Limits.Shapes.StrictInitial
import Mathbin.CategoryTheory.Limits.Shapes.CommSq
import Mathbin.Algebra.Category.Ring.Instances
import Mathbin.Topology.LocalAtTarget

/-!
# Open immersions of structured spaces

We say that a morphism of presheafed spaces `f : X ⟶ Y` is an open immersions if
the underlying map of spaces is an open embedding `f : X ⟶ U ⊆ Y`,
and the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.

Abbreviations are also provided for `SheafedSpace`, `LocallyRingedSpace` and `Scheme`.

## Main definitions

* `algebraic_geometry.PresheafedSpace.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a PresheafedSpace hom `f` is an open_immersion.
* `algebraic_geometry.is_open_immersion`: the `Prop`-valued typeclass asserting
  that a Scheme morphism `f` is an open_immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict`: The source of an
  open immersion is isomorphic to the restriction of the target onto the image.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.lift`: Any morphism whose range is
  contained in an open immersion factors though the open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace`: If `f : X ⟶ Y` is an
  open immersion of presheafed spaces, and `Y` is a sheafed space, then `X` is also a sheafed
  space. The morphism as morphisms of sheafed spaces is given by `to_SheafedSpace_hom`.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace`: If `f : X ⟶ Y` is
  an open immersion of presheafed spaces, and `Y` is a locally ringed space, then `X` is also a
  locally ringed space. The morphism as morphisms of locally ringed spaces is given by
  `to_LocallyRingedSpace_hom`.

## Main results

* `algebraic_geometry.PresheafedSpace.is_open_immersion.comp`: The composition of two open
  immersions is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso`: An iso is an open immersion.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso`:
  A surjective open immersion is an isomorphism.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso`: An open immersion induces
  an isomorphism on stalks.
* `algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left`: If `f` is an open
  immersion, then the pullback `(f, g)` exists (and the forgetful functor to `Top` preserves it).
* `algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left`: Open immersions
  are stable under pullbacks.
* `algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso` An (topological) open embedding
  between two sheafed spaces is an open immersion if all the stalk maps are isomorphisms.

-/


open TopologicalSpace CategoryTheory Opposite

open CategoryTheory.Limits

namespace AlgebraicGeometry

universe v v₁ v₂ u

variable {C : Type u} [Category.{v} C]

/-- An open immersion of PresheafedSpaces is an open embedding `f : X ⟶ U ⊆ Y` of the underlying
spaces, such that the sheaf map `Y(V) ⟶ f _* X(V)` is an iso for each `V ⊆ U`.
-/
class PresheafedSpace.IsOpenImmersion {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) : Prop where
  base_open : OpenEmbedding f.base
  c_iso : ∀ U : Opens X, IsIso (f.c.app (op (base_open.isOpenMap.functor.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion

/-- A morphism of SheafedSpaces is an open immersion if it is an open immersion as a morphism
of PresheafedSpaces
-/
abbrev SheafedSpace.IsOpenImmersion {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) : Prop :=
  PresheafedSpace.IsOpenImmersion f
#align algebraic_geometry.SheafedSpace.is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion

/-- A morphism of LocallyRingedSpaces is an open immersion if it is an open immersion as a morphism
of SheafedSpaces
-/
abbrev LocallyRingedSpace.IsOpenImmersion {X Y : LocallyRingedSpace} (f : X ⟶ Y) : Prop :=
  SheafedSpace.IsOpenImmersion f.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

/-- A morphism of Schemes is an open immersion if it is an open immersion as a morphism
of LocallyRingedSpaces
-/
abbrev IsOpenImmersion {X Y : Scheme} (f : X ⟶ Y) : Prop :=
  LocallyRingedSpace.IsOpenImmersion f
#align algebraic_geometry.is_open_immersion AlgebraicGeometry.IsOpenImmersion

namespace PresheafedSpace.IsOpenImmersion

open PresheafedSpace

-- mathport name: expris_open_immersion
local notation "is_open_immersion" => PresheafedSpace.IsOpenImmersion

attribute [instance] is_open_immersion.c_iso

section

variable {X Y : PresheafedSpace.{v} C} {f : X ⟶ Y} (H : is_open_immersion f)

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev openFunctor :=
  H.base_open.isOpenMap.functor
#align algebraic_geometry.PresheafedSpace.is_open_immersion.open_functor AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.openFunctor

/-- An open immersion `f : X ⟶ Y` induces an isomorphism `X ≅ Y|_{f(X)}`. -/
@[simps hom_c_app]
noncomputable def isoRestrict : X ≅ Y.restrict H.base_open :=
  PresheafedSpace.isoOfComponents (Iso.refl _)
    (by
      symm
      fapply NatIso.ofComponents
      intro U
      refine' asIso (f.c.app (op (H.open_functor.obj (unop U)))) ≪≫ X.presheaf.map_iso (eqToIso _)
      · induction U using Opposite.rec
        cases U
        dsimp only [IsOpenMap.functor, Functor.op, Opens.map]
        congr 2
        erw [Set.preimage_image_eq _ H.base_open.inj]
        rfl
      · intro U V i
        simp only [CategoryTheory.eqToIso.hom, TopCat.Presheaf.pushforwardObj_map, Category.assoc,
          Functor.op_map, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, ← X.presheaf.map_comp]
        erw [f.c.naturality_assoc, ← X.presheaf.map_comp]
        congr )
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict

@[simp]
theorem isoRestrict_hom_ofRestrict : H.isoRestrict.hom ≫ Y.ofRestrict _ = f :=
  by
  ext
  · simp only [comp_c_app, isoRestrict_hom_c_app, NatTrans.comp_app, eqToHom_refl, ofRestrict_c_app,
      Category.assoc, whiskerRight_id']
    erw [Category.comp_id, f.c.naturality_assoc, ← X.presheaf.map_comp]
    trans f.c.app x ≫ X.presheaf.map (𝟙 _)
    · congr
    · erw [X.presheaf.map_id, Category.comp_id]
  · rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_hom_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict

@[simp]
theorem isoRestrict_inv_ofRestrict : H.isoRestrict.inv ≫ f = Y.ofRestrict _ := by
  rw [Iso.inv_comp_eq, isoRestrict_hom_ofRestrict]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_restrict_inv_of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoRestrict_inv_ofRestrict

instance mono [H : is_open_immersion f] : Mono f :=
  by
  rw [← H.iso_restrict_hom_of_restrict]
  apply mono_comp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.mono AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.mono

/-- The composition of two open immersions is an open immersion. -/
instance comp {Z : PresheafedSpace C} (f : X ⟶ Y) [hf : is_open_immersion f] (g : Y ⟶ Z)
    [hg : is_open_immersion g] : is_open_immersion (f ≫ g)
    where
  base_open := hg.base_open.comp hf.base_open
  c_iso U := by
    generalize_proofs h
    dsimp only [AlgebraicGeometry.PresheafedSpace.comp_c_app, unop_op, Functor.op, comp_base,
      TopCat.Presheaf.pushforwardObj_obj, Opens.map_comp_obj]
    apply (config := { instances := false }) IsIso.comp_isIso
    swap
    · have : (Opens.map g.base).obj (h.functor.obj U) = hf.open_functor.obj U :=
        by
        dsimp only [Opens.map, IsOpenMap.functor, PresheafedSpace.comp_base]
        congr 1
        rw [coe_comp, ← Set.image_image, Set.preimage_image_eq _ hg.base_open.inj]
      rw [this]
      infer_instance
    · have : h.functor.obj U = hg.open_functor.obj (hf.open_functor.obj U) :=
        by
        dsimp only [IsOpenMap.functor]
        congr 1
        rw [comp_base, coe_comp, ← Set.image_image]
        congr
      rw [this]
      infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.comp AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.comp

/-- For an open immersion `f : X ⟶ Y` and an open set `U ⊆ X`, we have the map `X(U) ⟶ Y(U)`. -/
noncomputable def invApp (U : Opens X) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (H.openFunctor.obj U)) :=
  X.presheaf.map (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.inj])) ≫
    inv (f.c.app (op (H.openFunctor.obj U)))
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp

@[simp, reassoc.1]
theorem inv_naturality {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    X.presheaf.map i ≫ H.invApp (unop V) =
      H.invApp (unop U) ≫ Y.presheaf.map (H.openFunctor.op.map i) :=
  by
  simp only [invApp, ← Category.assoc]
  rw [IsIso.comp_inv_eq]
  simp only [Category.assoc, f.c.naturality, IsIso.inv_hom_id_assoc, ← X.presheaf.map_comp]
  erw [← X.presheaf.map_comp]
  congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_naturality AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_naturality

instance (U : Opens X) : IsIso (H.invApp U) :=
  by
  delta inv_app
  infer_instance

theorem inv_invApp (U : Opens X) :
    inv (H.invApp U) =
      f.c.app (op (H.openFunctor.obj U)) ≫
        X.presheaf.map (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.inj])) :=
  by
  rw [← cancel_epi (H.inv_app U)]
  rw [IsIso.hom_inv_id]
  delta inv_app
  simp [← Functor.map_comp]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.inv_invApp

@[simp, reassoc.1, elementwise]
theorem invApp_app (U : Opens X) :
    H.invApp U ≫ f.c.app (op (H.openFunctor.obj U)) =
      X.presheaf.map (eqToHom (by simp [Opens.map, Set.preimage_image_eq _ H.base_open.inj])) :=
  by rw [invApp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.inv_app_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.invApp_app

@[simp, reassoc.1]
theorem app_invApp (U : Opens Y) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.presheaf.map
        ((homOfLe (Set.image_preimage_subset f.base U)).op :
          op U ⟶ op (H.openFunctor.obj ((Opens.map f.base).obj U))) :=
  by
  erw [← Category.assoc]
  rw [IsIso.comp_inv_eq, f.c.naturality]
  congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_invApp

/-- A variant of `app_inv_app` that gives an `eq_to_hom` instead of `hom_of_le`. -/
@[reassoc.1]
theorem app_inv_app' (U : Opens Y) (hU : (U : Set Y) ⊆ Set.range f.base) :
    f.c.app (op U) ≫ H.invApp ((Opens.map f.base).obj U) =
      Y.presheaf.map
        (eqToHom
            (by
              apply LE.le.antisymm
              · exact Set.image_preimage_subset f.base U.1
              · change U ⊆ _
                refine' LE.le.trans_eq _ (@set.image_preimage_eq_inter_range _ _ f.base U.1).symm
                exact set.subset_inter_iff.mpr ⟨fun _ h => h, hU⟩)).op :=
  by
  erw [← Category.assoc]
  rw [IsIso.comp_inv_eq, f.c.naturality]
  congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.app_inv_app' AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.app_inv_app'

/-- An isomorphism is an open immersion. -/
instance ofIso {X Y : PresheafedSpace.{v} C} (H : X ≅ Y) : is_open_immersion H.hom
    where
  base_open := (TopCat.homeoOfIso ((forget C).mapIso H)).openEmbedding
  c_iso _ := inferInstance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso

instance (priority := 100) ofIsIso {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] :
    is_open_immersion f :=
  AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIso (asIso f)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofIsIso

instance ofRestrict {X : TopCat} (Y : PresheafedSpace C) {f : X ⟶ Y.carrier}
    (hf : OpenEmbedding f) : is_open_immersion (Y.ofRestrict hf)
    where
  base_open := hf
  c_iso U := by
    dsimp
    have : (Opens.map f).obj (hf.is_open_map.functor.obj U) = U :=
      by
      cases U
      dsimp only [Opens.map, IsOpenMap.functor]
      congr 1
      rw [Set.preimage_image_eq _ hf.inj]
      rfl
    convert show IsIso (Y.presheaf.map (𝟙 _)) from inferInstance
    · apply Subsingleton.helim
      rw [this]
    · rw [Y.presheaf.map_id]
      infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict

@[elementwise, simp]
theorem ofRestrict_invApp {C : Type _} [Category C] (X : PresheafedSpace C) {Y : TopCat}
    {f : Y ⟶ TopCat.of X.carrier} (h : OpenEmbedding f) (U : Opens (X.restrict h).carrier) :
    (PresheafedSpace.IsOpenImmersion.ofRestrict X h).invApp U = 𝟙 _ :=
  by
  delta PresheafedSpace.is_open_immersion.inv_app
  rw [IsIso.comp_inv_eq, Category.id_comp]
  change X.presheaf.map _ = X.presheaf.map _
  congr
#align algebraic_geometry.PresheafedSpace.is_open_immersion.of_restrict_inv_app AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.ofRestrict_invApp

/-- An open immersion is an iso if the underlying continuous map is epi. -/
theorem to_iso (f : X ⟶ Y) [h : is_open_immersion f] [h' : Epi f.base] : IsIso f :=
  by
  apply (config := { instances := false }) isIso_of_components
  · let this : X ≃ₜ Y :=
      (Homeomorph.ofEmbedding _ h.base_open.to_embedding).trans
        { toFun := Subtype.val
          invFun := fun x =>
            ⟨x, by
              rw [set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp h')]
              trivial⟩
          left_inv := fun ⟨_, _⟩ => rfl
          right_inv := fun _ => rfl }
    convert IsIso.of_iso (TopCat.isoOfHomeo this)
    · ext
      rfl
  · apply (config := { instances := false }) NatIso.isIso_of_isIso_app
    intro U
    have : U = op (h.open_functor.obj ((Opens.map f.base).obj (unop U))) :=
      by
      induction U using Opposite.rec
      cases U
      dsimp only [Functor.op, Opens.map]
      congr
      exact (Set.image_preimage_eq _ ((TopCat.epi_iff_surjective _).mp h')).symm
    convert @is_open_immersion.c_iso _ h ((Opens.map f.base).obj (unop U))
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.to_iso

instance stalk_iso [HasColimits C] [H : is_open_immersion f] (x : X) : IsIso (stalkMap f x) :=
  by
  rw [← H.iso_restrict_hom_of_restrict]
  rw [PresheafedSpace.stalkMap.comp]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.stalk_iso AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.stalk_iso

end

section Pullback

noncomputable section

variable {X Y Z : PresheafedSpace.{v} C} (f : X ⟶ Z) [hf : is_open_immersion f] (g : Y ⟶ Z)

include hf

/-- (Implementation.) The projection map when constructing the pullback along an open immersion.
-/
def pullbackConeOfLeftFst :
    Y.restrict (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base) ⟶ X
    where
  base := pullback.fst
  c :=
    { app := fun U =>
        hf.invApp (unop U) ≫
          g.c.app (op (hf.base_open.isOpenMap.functor.obj (unop U))) ≫
            Y.presheaf.map
              (eqToHom
                (by
                  simp only [IsOpenMap.functor, Subtype.mk_eq_mk, unop_op, op_inj_iff, Opens.map,
                    Subtype.coe_mk, Functor.op_obj, Subtype.val_eq_coe]
                  apply LE.le.antisymm
                  · rintro _ ⟨_, h₁, h₂⟩
                    use (TopCat.pullbackIsoProdSubtype _ _).inv ⟨⟨_, _⟩, h₂⟩
                    simpa using h₁
                  · rintro _ ⟨x, h₁, rfl⟩
                    exact ⟨_, h₁, ConcreteCategory.congr_hom pullback.condition x⟩))
      naturality' := by
        intro U V i
        induction U using Opposite.rec
        induction V using Opposite.rec
        simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforwardObj_map, Category.assoc,
          NatTrans.naturality_assoc, Functor.op_map, inv_naturality_assoc, ← Y.presheaf.map_comp]
        erw [← Y.presheaf.map_comp]
        congr }
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst

theorem pullback_cone_of_left_condition : pullbackConeOfLeftFst f g ≫ f = Y.ofRestrict _ ≫ g :=
  by
  ext U
  · induction U using Opposite.rec
    dsimp only [comp_c_app, NatTrans.comp_app, unop_op, whiskerRight_app, pullbackConeOfLeftFst]
    simp only [Quiver.Hom.unop_op, TopCat.Presheaf.pushforwardObj_map, app_invApp_assoc,
      eqToHom_app, eqToHom_unop, Category.assoc, NatTrans.naturality_assoc, Functor.op_map]
    erw [← Y.presheaf.map_comp, ← Y.presheaf.map_comp]
    congr
  · simpa using pullback.condition
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_condition AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition

/-- We construct the pullback along an open immersion via restricting along the pullback of the
maps of underlying spaces (which is also an open embedding).
-/
def pullbackConeOfLeft : PullbackCone f g :=
  PullbackCone.mk (pullbackConeOfLeftFst f g) (Y.ofRestrict _) (pullback_cone_of_left_condition f g)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeft

variable (s : PullbackCone f g)

/-- (Implementation.) Any cone over `cospan f g` indeed factors through the constructed cone.
-/
def pullbackConeOfLeftLift : s.x ⟶ (pullbackConeOfLeft f g).x
    where
  base :=
    pullback.lift s.fst.base s.snd.base
      (congr_arg (fun x => PresheafedSpace.Hom.base x) s.condition)
  c :=
    { app := fun U =>
        s.snd.c.app _ ≫
          s.x.presheaf.map
            (eqToHom
              (by
                dsimp only [Opens.map, IsOpenMap.functor, Functor.op]
                congr 2
                let s' : PullbackCone f.base g.base := PullbackCone.mk s.fst.base s.snd.base _
                have : _ = s.snd.base := limit.lift_π s' WalkingCospan.right
                conv_lhs =>
                  erw [← this]
                  rw [coe_comp]
                  erw [← Set.preimage_preimage]
                erw [Set.preimage_image_eq _
                    (TopCat.snd_openEmbedding_of_left_openEmbedding hf.base_open g.base).inj]
                simp))
      naturality' := fun U V i => by
        erw [s.snd.c.naturality_assoc]
        rw [Category.assoc]
        erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
        congr }
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_fst :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).fst = s.fst :=
  by
  ext x
  · induction x using Opposite.rec
    change ((_ ≫ _) ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [← s.X.presheaf.map_comp]
    erw [s.snd.c.naturality_assoc]
    have := congr_app s.condition (op (hf.open_functor.obj x))
    dsimp only [comp_c_app, unop_op] at this
    rw [← IsIso.comp_inv_eq] at this
    reassoc! this
    erw [← this, hf.inv_app_app_assoc, s.fst.c.naturality_assoc]
    simpa [eqToHom_map]
  · change pullback.lift _ _ _ ≫ pullback.fst = _
    simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_fst AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst

-- this lemma is not a `simp` lemma, because it is an implementation detail
theorem pullbackConeOfLeftLift_snd :
    pullbackConeOfLeftLift f g s ≫ (pullbackConeOfLeft f g).snd = s.snd :=
  by
  ext x
  · change (_ ≫ _ ≫ _) ≫ _ = _
    simp_rw [Category.assoc]
    erw [s.snd.c.naturality_assoc]
    erw [← s.X.presheaf.map_comp, ← s.X.presheaf.map_comp]
    trans s.snd.c.app x ≫ s.X.presheaf.map (𝟙 _)
    · congr
    · rw [s.X.presheaf.map_id]
      erw [Category.comp_id]
  · change pullback.lift _ _ _ ≫ pullback.snd = _
    simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_lift_snd AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd

instance pullbackConeSndIsOpenImmersion : is_open_immersion (pullbackConeOfLeft f g).snd :=
  by
  erw [CategoryTheory.Limits.PullbackCone.mk_snd]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_snd_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeSndIsOpenImmersion

/-- The constructed pullback cone is indeed the pullback. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  by
  apply PullbackCone.isLimitAux'
  intro s
  use pullbackConeOfLeftLift f g s
  use pullbackConeOfLeftLift_fst f g s
  use pullbackConeOfLeftLift_snd f g s
  intro m h₁ h₂
  rw [← cancel_mono (pullbackConeOfLeft f g).snd]
  exact h₂.trans (pullbackConeOfLeftLift_snd f g s).symm
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullbackSndOfLeft : is_open_immersion (pullback.snd : pullback f g ⟶ _) :=
  by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackSndOfLeft

/-- Open immersions are stable under base-change. -/
instance pullbackFstOfRight : is_open_immersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackFstOfRight

instance pullbackToBaseIsOpenImmersion [is_open_immersion g] :
    is_open_immersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullbackToBaseIsOpenImmersion

instance forgetPreservesLimitsOfLeft : PreservesLimit (cospan f g) (forget C) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (IsLimit.postcomposeHomEquiv (diagramIsoCospan.{v} _) _).toFun
      refine' (IsLimit.equivIsoLimit _).toFun (limit.isLimit (cospan f.base g.base))
      fapply Cones.ext
      exact Iso.refl _
      change ∀ j, _ = 𝟙 _ ≫ _ ≫ _
      simp_rw [Category.id_comp]
      rintro (_ | _ | _) <;> symm
      · erw [Category.comp_id]
        exact limit.w (cospan f.base g.base) WalkingCospan.Hom.inl
      · exact Category.comp_id _
      · exact Category.comp_id _)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_left AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfLeft

instance forgetPreservesLimitsOfRight : PreservesLimit (cospan g f) (forget C) :=
  preservesPullbackSymmetry (forget C) f g
#align algebraic_geometry.PresheafedSpace.is_open_immersion.forget_preserves_limits_of_right AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.forgetPreservesLimitsOfRight

theorem pullback_snd_isIso_of_range_subset (H : Set.range g.base ⊆ Set.range f.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) :=
  by
  haveI := TopCat.snd_iso_of_left_embedding_range_subset hf.base_open.to_embedding g.base H
  have : IsIso (pullback.snd : pullback f g ⟶ _).base :=
    by
    delta pullback.snd
    rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
    change IsIso (_ ≫ pullback.snd)
    infer_instance
  apply to_iso
#align algebraic_geometry.PresheafedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H : Set.range g.base ⊆ Set.range f.base) : Y ⟶ X :=
  haveI := pullback_snd_isIso_of_range_subset f g H
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift

@[simp, reassoc.1]
theorem lift_fac (H : Set.range g.base ⊆ Set.range f.base) : lift f g H ≫ f = g :=
  by
  erw [Category.assoc]
  rw [IsIso.inv_comp_eq]
  exact pullback.condition
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_fac AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H : Set.range g.base ⊆ Set.range f.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H := by rw [← cancel_mono f, hl, lift_fac]
#align algebraic_geometry.PresheafedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range is isomorphic. -/
@[simps]
def isoOfRangeEq [is_open_immersion g] (e : Set.range f.base = Set.range g.base) : X ≅ Y
    where
  Hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id' := by
    rw [← cancel_mono f]
    simp
  inv_hom_id' := by
    rw [← cancel_mono g]
    simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.iso_of_range_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isoOfRangeEq

end Pullback

open CategoryTheory.Limits.WalkingCospan

section ToSheafedSpace

variable {X : PresheafedSpace.{v} C} (Y : SheafedSpace C)

variable (f : X ⟶ Y.toPresheafedSpace) [H : is_open_immersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a SheafedSpace, then so is `X`. -/
def toSheafedSpace : SheafedSpace C
    where
  IsSheaf :=
    by
    apply TopCat.Presheaf.isSheaf_of_iso (sheafIsoOfIso H.iso_restrict.symm).symm
    apply TopCat.Sheaf.pushforward_sheaf_of_sheaf
    exact (Y.restrict H.base_open).isSheaf
  toPresheafedSpace := X
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace

@[simp]
theorem toSheafedSpace_toPresheafedSpace : (toSheafedSpace Y f).toPresheafedSpace = X :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_to_PresheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_toPresheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a SheafedSpace, we can
upgrade it into a morphism of SheafedSpaces.
-/
def toSheafedSpaceHom : toSheafedSpace Y f ⟶ Y :=
  f
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom

@[simp]
theorem toSheafedSpaceHom_base : (toSheafedSpaceHom Y f).base = f.base :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_base AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_base

@[simp]
theorem toSheafedSpaceHom_c : (toSheafedSpaceHom Y f).c = f.c :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_hom_c AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpaceHom_c

instance toSheafedSpace_isOpenImmersion : SheafedSpace.IsOpenImmersion (toSheafedSpaceHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_SheafedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSheafedSpace_isOpenImmersion

omit H

@[simp]
theorem sheafedSpace_toSheafedSpace {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [is_open_immersion f] :
    toSheafedSpace Y f = X := by
  cases X
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.SheafedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.sheafedSpace_toSheafedSpace

end ToSheafedSpace

section ToLocallyRingedSpace

variable {X : PresheafedSpace.{u} CommRingCat.{u}} (Y : LocallyRingedSpace.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : is_open_immersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a LocallyRingedSpace, then so is `X`. -/
def toLocallyRingedSpace : LocallyRingedSpace
    where
  toSheafedSpace := toSheafedSpace Y.toSheafedSpace f
  LocalRing x :=
    haveI : LocalRing (Y.to_SheafedSpace.to_PresheafedSpace.stalk (f.base x)) := Y.local_ring _
    (asIso (stalkMap f x)).commRingIsoToRingEquiv.localRing
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace

@[simp]
theorem toLocallyRingedSpace_toSheafedSpace :
    (toLocallyRingedSpace Y f).toSheafedSpace = toSheafedSpace Y.1 f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_to_SheafedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_toSheafedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a LocallyRingedSpace, we can
upgrade it into a morphism of LocallyRingedSpace.
-/
def toLocallyRingedSpaceHom : toLocallyRingedSpace Y f ⟶ Y :=
  ⟨f, fun x => inferInstance⟩
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom

@[simp]
theorem toLocallyRingedSpaceHom_val : (toLocallyRingedSpaceHom Y f).val = f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_hom_val AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpaceHom_val

instance toLocallyRingedSpace_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (toLocallyRingedSpaceHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_LocallyRingedSpace_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toLocallyRingedSpace_isOpenImmersion

omit H

@[simp]
theorem locallyRingedSpace_toLocallyRingedSpace {X Y : LocallyRingedSpace} (f : X ⟶ Y)
    [LocallyRingedSpace.IsOpenImmersion f] : toLocallyRingedSpace Y f.1 = X :=
  by
  cases X
  delta to_LocallyRingedSpace
  simp
#align algebraic_geometry.PresheafedSpace.is_open_immersion.LocallyRingedSpace_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.locallyRingedSpace_toLocallyRingedSpace

end ToLocallyRingedSpace

theorem isIso_of_subset {X Y : PresheafedSpace.{v} C} (f : X ⟶ Y)
    [H : PresheafedSpace.IsOpenImmersion f] (U : Opens Y.carrier)
    (hU : (U : Set Y.carrier) ⊆ Set.range f.base) : IsIso (f.c.app <| op U) :=
  by
  have : U = H.base_open.is_open_map.functor.obj ((Opens.map f.base).obj U) :=
    by
    ext1
    exact (set.inter_eq_left_iff_subset.mpr hU).symm.trans set.image_preimage_eq_inter_range.symm
  convert PresheafedSpace.IsOpenImmersion.c_iso ((Opens.map f.base).obj U)
#align algebraic_geometry.PresheafedSpace.is_open_immersion.is_iso_of_subset AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.isIso_of_subset

end PresheafedSpace.IsOpenImmersion

namespace SheafedSpace.IsOpenImmersion

instance (priority := 100) of_isIso {X Y : SheafedSpace.{v} C} (f : X ⟶ Y) [IsIso f] :
    SheafedSpace.IsOpenImmersion f :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ f (SheafedSpace.forgetToPresheafedSpace.map_isIso _)
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_isIso

instance comp {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) [SheafedSpace.IsOpenImmersion f]
    [SheafedSpace.IsOpenImmersion g] : SheafedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f g
#align algebraic_geometry.SheafedSpace.is_open_immersion.comp AlgebraicGeometry.SheafedSpace.IsOpenImmersion.comp

section Pullback

variable {X Y Z : SheafedSpace C} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : SheafedSpace.IsOpenImmersion f]

include H

-- mathport name: exprforget
local notation "forget" => SheafedSpace.forgetToPresheafedSpace

open CategoryTheory.Limits.WalkingCospan

instance : Mono f :=
  forget.mono_of_mono_map (show @Mono (PresheafedSpace C) _ _ _ f by infer_instance)

instance forgetMapIsOpenImmersion : PresheafedSpace.IsOpenImmersion (forget.map f) :=
  ⟨H.base_open, H.c_iso⟩
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetMapIsOpenImmersion

instance hasLimitCospanForgetOfLeft : HasLimit (cospan f g ⋙ forget) :=
  by
  apply hasLimitOfIso (diagramIsoCospan.{v} _).symm
  change HasLimit (cospan (forget.map f) (forget.map g))
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimitCospanForgetOfLeft

instance hasLimitCospanForgetOfLeft' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map f) (forget.map g)) from inferInstance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimitCospanForgetOfLeft'

instance hasLimitCospanForgetOfRight : HasLimit (cospan g f ⋙ forget) :=
  by
  apply hasLimitOfIso (diagramIsoCospan.{v} _).symm
  change HasLimit (cospan (forget.map g) (forget.map f))
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimitCospanForgetOfRight

instance hasLimitCospanForgetOfRight' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map g) (forget.map f)) from inferInstance
#align algebraic_geometry.SheafedSpace.is_open_immersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.SheafedSpace.IsOpenImmersion.hasLimitCospanForgetOfRight'

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.snd (PresheafedSpace C) _ _ _ _ f g _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr ) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfLeft

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toSheafedSpace Y
      (@pullback.fst (PresheafedSpace C) _ _ _ _ g f _))
    (eqToIso (show pullback _ _ = pullback _ _ by congr ) ≪≫
      HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.SheafedSpace.is_open_immersion.forget_creates_pullback_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.forgetCreatesPullbackOfRight

instance sheafedSpaceForgetPreservesOfLeft : PreservesLimit (cospan f g) (SheafedSpace.forget C) :=
  @Limits.compPreservesLimit _ _ _ _ forget (PresheafedSpace.forget C) _
    (by
      apply (config := { instances := true })
        preservesLimitOfIsoDiagram _ (diagramIsoCospan.{v} _).symm
      dsimp
      infer_instance)
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpaceForgetPreservesOfLeft

instance sheafedSpaceForgetPreservesOfRight : PreservesLimit (cospan g f) (SheafedSpace.forget C) :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_forget_preserves_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpaceForgetPreservesOfRight

instance sheafedSpace_hasPullback_of_left : HasPullback f g :=
  hasLimitOfCreated (cospan f g) forget
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_left

instance sheafedSpace_hasPullback_of_right : HasPullback g f :=
  hasLimitOfCreated (cospan g f) forget
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_has_pullback_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance sheafedSpace_pullback_snd_of_left :
    SheafedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) :=
  by
  delta pullback.snd
  have : _ = limit.π (cospan f g) right := preserves_limits_iso_hom_π forget (cospan f g) right
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan.{v} (cospan f g ⋙ forget)) right
  erw [Category.comp_id] at this
  rw [← this]
  dsimp
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_snd_of_left AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_snd_of_left

instance sheafedSpace_pullback_fst_of_right :
    SheafedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  delta pullback.fst
  have : _ = limit.π (cospan g f) left := preserves_limits_iso_hom_π forget (cospan g f) left
  rw [← this]
  have := HasLimit.isoOfNatIso_hom_π (diagramIsoCospan.{v} (cospan g f ⋙ forget)) left
  erw [Category.comp_id] at this
  rw [← this]
  dsimp
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_fst_of_right AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_fst_of_right

instance sheafedSpace_pullback_to_base_isOpenImmersion [SheafedSpace.IsOpenImmersion g] :
    SheafedSpace.IsOpenImmersion (limit.π (cospan f g) one : pullback f g ⟶ Z) :=
  by
  rw [← limit.w (cospan f g) Hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.SheafedSpace.is_open_immersion.SheafedSpace_pullback_to_base_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sheafedSpace_pullback_to_base_isOpenImmersion

end Pullback

section OfStalkIso

variable [HasLimits C] [HasColimits C] [ConcreteCategory.{v} C]

variable [ReflectsIsomorphisms (forget C)] [PreservesLimits (forget C)]

variable [PreservesFilteredColimits (forget C)]

/-- Suppose `X Y : SheafedSpace C`, where `C` is a concrete category,
whose forgetful functor reflects isomorphisms, preserves limits and filtered colimits.
Then a morphism `X ⟶ Y` that is a topological open embedding
is an open immersion iff every stalk map is an iso.
-/
theorem of_stalk_iso {X Y : SheafedSpace C} (f : X ⟶ Y) (hf : OpenEmbedding f.base)
    [H : ∀ x : X, IsIso (PresheafedSpace.stalkMap f x)] : SheafedSpace.IsOpenImmersion f :=
  { base_open := hf
    c_iso := fun U =>
      by
      apply (config := { instances := false })
        TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso
          (show Y.sheaf ⟶ (TopCat.Sheaf.pushforward f.base).obj X.sheaf from ⟨f.c⟩)
      rintro ⟨_, y, hy, rfl⟩
      specialize H y
      delta PresheafedSpace.stalk_map at H
      haveI H' :=
        TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_openEmbedding C hf X.presheaf y
      have := @is_iso.comp_is_iso _ H (@is_iso.inv_is_iso _ H')
      rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at this
      exact this }
#align algebraic_geometry.SheafedSpace.is_open_immersion.of_stalk_iso AlgebraicGeometry.SheafedSpace.IsOpenImmersion.of_stalk_iso

end OfStalkIso

section Prod

variable [HasLimits C] {ι : Type v} (F : Discrete ι ⥤ SheafedSpace C) [HasColimit F]
  (i : Discrete ι)

theorem sigma_ι_openEmbedding : OpenEmbedding (colimit.ι F i).base :=
  by
  rw [← show _ = (colimit.ι F i).base from ι_preserves_colimits_iso_inv (SheafedSpace.forget C) F i]
  have : _ = _ ≫ colimit.ι (Discrete.functor ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk)) i :=
    HasColimit.isoOfNatIso_ι_hom Discrete.natIsoFunctor i
  rw [← Iso.eq_comp_inv] at this
  rw [this]
  have : colimit.ι _ _ ≫ _ = _ :=
    TopCat.sigmaIsoSigma_hom_ι.{v, v} ((F ⋙ SheafedSpace.forget C).obj ∘ Discrete.mk) i.as
  rw [← Iso.eq_comp_inv] at this
  cases i
  rw [this]
  simp_rw [← Category.assoc, TopCat.openEmbedding_iff_comp_isIso,
    TopCat.openEmbedding_iff_isIso_comp]
  dsimp
  exact openEmbedding_sigmaMk
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_open_embedding AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_openEmbedding

theorem image_preimage_is_empty (j : Discrete ι) (h : i ≠ j) (U : Opens (F.obj i)) :
    (Opens.map (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) j).base).obj
        ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
          ((sigma_ι_openEmbedding F i).isOpenMap.functor.obj U)) =
      ∅ :=
  by
  ext
  apply iff_false_intro
  rintro ⟨y, hy, eq⟩
  replace eq :=
    ConcreteCategory.congr_arg
      (preservesColimitIso (SheafedSpace.forget C) F ≪≫
          HasColimit.isoOfNatIso Discrete.natIsoFunctor ≪≫ TopCat.sigmaIsoSigma.{v} _).hom
      eq
  simp_rw [CategoryTheory.Iso.trans_hom, ← TopCat.comp_app, ← PresheafedSpace.comp_base] at eq
  rw [ι_preserves_colimits_iso_inv] at eq
  change
    ((SheafedSpace.forget C).map (colimit.ι F i) ≫ _) y =
      ((SheafedSpace.forget C).map (colimit.ι F j) ≫ _) x at
    eq
  cases i; cases j
  rw [ι_preserves_colimits_iso_hom_assoc, ι_preserves_colimits_iso_hom_assoc,
    HasColimit.isoOfNatIso_ι_hom_assoc, HasColimit.isoOfNatIso_ι_hom_assoc,
    TopCat.sigmaIsoSigma_hom_ι.{v}, TopCat.sigmaIsoSigma_hom_ι.{v}] at eq
  exact h (congr_arg Discrete.mk (congr_arg Sigma.fst eq))
#align algebraic_geometry.SheafedSpace.is_open_immersion.image_preimage_is_empty AlgebraicGeometry.SheafedSpace.IsOpenImmersion.image_preimage_is_empty

instance sigma_ι_isOpenImmersion [HasStrictTerminalObjects C] :
    SheafedSpace.IsOpenImmersion (colimit.ι F i)
    where
  base_open := sigma_ι_openEmbedding F i
  c_iso U :=
    by
    have e : colimit.ι F i = _ :=
      (ι_preserves_colimits_iso_inv SheafedSpace.forgetToPresheafedSpace F i).symm
    have H :
      OpenEmbedding
        (colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
            (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).base :=
      e ▸ sigma_ι_openEmbedding F i
    suffices
      IsIso
        ((colimit.ι (F ⋙ SheafedSpace.forgetToPresheafedSpace) i ≫
                (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv).c.app
          (op (H.is_open_map.functor.obj U)))
      by convert this
    rw [PresheafedSpace.comp_c_app, ← PresheafedSpace.colimitPresheafObjIsoComponentwiseLimit_hom_π]
    rsuffices :
      IsIso
        (limit.π
          (PresheafedSpace.componentwiseDiagram (F ⋙ SheafedSpace.forgetToPresheafedSpace)
            ((Opens.map (preservesColimitIso SheafedSpace.forgetToPresheafedSpace F).inv.base).obj
              (unop <| op <| H.is_open_map.functor.obj U)))
          (op i))
    · infer_instance
    apply limit_π_isIso_of_is_strict_terminal
    intro j hj
    induction j using Opposite.rec
    dsimp
    convert (F.obj j).sheaf.isTerminalOfEmpty
    convert image_preimage_is_empty F i j (fun h => hj (congr_arg op h.symm)) U
    exact (congr_arg PresheafedSpace.Hom.base e).symm
#align algebraic_geometry.SheafedSpace.is_open_immersion.sigma_ι_is_open_immersion AlgebraicGeometry.SheafedSpace.IsOpenImmersion.sigma_ι_isOpenImmersion

end Prod

end SheafedSpace.IsOpenImmersion

namespace LocallyRingedSpace.IsOpenImmersion

section Pullback

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : LocallyRingedSpace.IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : LocallyRingedSpace.IsOpenImmersion g :=
  @PresheafedSpace.IsOpenImmersion.ofIsIso _ g.1
    ⟨⟨(inv g).1, by
        erw [← LocallyRingedSpace.comp_val]
        rw [IsIso.hom_inv_id]
        erw [← LocallyRingedSpace.comp_val]
        rw [IsIso.inv_hom_id]
        constructor <;> simpa⟩⟩
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.of_is_iso AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_isIso

include H

instance comp (g : Z ⟶ Y) [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (f ≫ g) :=
  PresheafedSpace.IsOpenImmersion.comp f.1 g.1
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.comp AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.comp

instance mono : Mono f :=
  LocallyRingedSpace.forgetToSheafedSpace.mono_of_mono_map (show Mono f.1 by infer_instance)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.mono AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.mono

instance : SheafedSpace.IsOpenImmersion (LocallyRingedSpace.forgetToSheafedSpace.map f) :=
  H

/-- An explicit pullback cone over `cospan f g` if `f` is an open immersion. -/
def pullbackConeOfLeft : PullbackCone f g :=
  by
  refine'
    PullbackCone.mk _
      (Y.of_restrict (TopCat.snd_openEmbedding_of_left_openEmbedding H.base_open g.1.base)) _
  · use PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftFst f.1 g.1
    intro x
    have :=
      PresheafedSpace.stalkMap.congr_hom _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition f.1 g.1) x
    rw [PresheafedSpace.stalkMap.comp, PresheafedSpace.stalkMap.comp] at this
    rw [← IsIso.eq_inv_comp] at this
    rw [this]
    infer_instance
  ·
    exact
      LocallyRingedSpace.Hom.ext _ _
        (PresheafedSpace.IsOpenImmersion.pullback_cone_of_left_condition _ _)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeft

instance : LocallyRingedSpace.IsOpenImmersion (pullbackConeOfLeft f g).snd :=
  show PresheafedSpace.IsOpenImmersion (Y.toPresheafedSpace.ofRestrict _) by infer_instance

/-- The constructed `pullback_cone_of_left` is indeed limiting. -/
def pullbackConeOfLeftIsLimit : IsLimit (pullbackConeOfLeft f g) :=
  PullbackCone.isLimitAux' _ fun s =>
    by
    use
      PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift f.1 g.1
        (PullbackCone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.Hom.val s.condition))
    · intro x
      have :=
        PresheafedSpace.stalkMap.congr_hom _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1
            (PullbackCone.mk s.fst.1 s.snd.1 (congr_arg LocallyRingedSpace.Hom.val s.condition)))
          x
      change _ = _ ≫ PresheafedSpace.stalkMap s.snd.1 x at this
      rw [PresheafedSpace.stalkMap.comp, ← IsIso.eq_inv_comp] at this
      rw [this]
      infer_instance
    constructor
    ·
      exact
        LocallyRingedSpace.Hom.ext _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_fst f.1 g.1 _)
    constructor
    ·
      exact
        LocallyRingedSpace.Hom.ext _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1 _)
    intro m h₁ h₂
    rw [← cancel_mono (pullbackConeOfLeft f g).snd]
    exact
      h₂.trans
        (LocallyRingedSpace.Hom.ext _ _
          (PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftLift_snd f.1 g.1
              (PullbackCone.mk s.fst.1 s.snd.1
                (congr_arg LocallyRingedSpace.Hom.val s.condition))).symm)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_cone_of_left_is_limit AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit

instance hasPullback_of_left : HasPullback f g :=
  ⟨⟨⟨_, pullbackConeOfLeftIsLimit f g⟩⟩⟩
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasPullback_symmetry f g
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.has_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.hasPullback_of_right

/-- Open immersions are stable under base-change. -/
instance pullback_snd_of_left :
    LocallyRingedSpace.IsOpenImmersion (pullback.snd : pullback f g ⟶ _) :=
  by
  delta pullback.snd
  rw [← limit.isoLimitCone_hom_π ⟨_, pullbackConeOfLeftIsLimit f g⟩ WalkingCospan.right]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_of_left

/-- Open immersions are stable under base-change. -/
instance pullback_fst_of_right :
    LocallyRingedSpace.IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base_isOpenImmersion [LocallyRingedSpace.IsOpenImmersion g] :
    LocallyRingedSpace.IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl, cospan_map_inl]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_to_base_is_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_to_base_isOpenImmersion

instance forgetPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
      apply isLimitOfIsLimitPullbackConeMap SheafedSpace.forgetToPresheafedSpace
      exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetPreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesPullbackOfLeft :
    PreservesLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesLimitOfPreservesLimitCone (pullbackConeOfLeftIsLimit f g)
    (by
      apply (isLimitMapConePullbackConeEquiv _ _).symm.toFun
      exact PresheafedSpace.IsOpenImmersion.pullbackConeOfLeftIsLimit f.1 g.1)
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfLeft

instance forgetToPresheafedSpacePreservesOpenImmersion :
    PresheafedSpace.IsOpenImmersion
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).map f) :=
  H
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_open_immersion AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesOpenImmersion

instance forgetToTopPreservesPullbackOfLeft :
    PreservesLimit (cospan f g) (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _) :=
  by
  change
    PreservesLimit _
      ((LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) ⋙
        PresheafedSpace.forget _)
  apply (config := { instances := false }) Limits.compPreservesLimit
  infer_instance
  apply preservesLimitOfIsoDiagram _ (diagramIsoCospan.{u} _).symm
  dsimp [SheafedSpace.forgetToPresheafedSpace]
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_Top_preserves_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToTopPreservesPullbackOfLeft

instance forgetReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetReflectsPullbackOfLeft

instance forgetPreservesPullbackOfRight :
    PreservesLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetPreservesPullbackOfRight

instance forgetToPresheafedSpacePreservesPullbackOfRight :
    PreservesLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_preserves_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpacePreservesPullbackOfRight

instance forgetReflectsPullbackOfRight :
    ReflectsLimit (cospan g f) LocallyRingedSpace.forgetToSheafedSpace :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetReflectsPullbackOfRight

instance forgetToPresheafedSpaceReflectsPullbackOfLeft :
    ReflectsLimit (cospan f g)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_reflects_pullback_of_left AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfLeft

instance forgetToPresheafedSpaceReflectsPullbackOfRight :
    ReflectsLimit (cospan g f)
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) :=
  reflectsLimitOfReflectsIsomorphisms _ _
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.forget_to_PresheafedSpace_reflects_pullback_of_right AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.forgetToPresheafedSpaceReflectsPullbackOfRight

theorem pullback_snd_isIso_of_range_subset (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    IsIso (pullback.snd : pullback f g ⟶ _) :=
  by
  apply (config := { instances := false })
    ReflectsIsomorphisms.reflects LocallyRingedSpace.forgetToSheafedSpace
  apply (config := { instances := false })
    ReflectsIsomorphisms.reflects SheafedSpace.forgetToPresheafedSpace
  erw [←
    PreservesPullback.iso_hom_snd
      (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace) f g]
  haveI := PresheafedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset _ _ H'
  infer_instance
  infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.pullback_snd_is_iso_of_range_subset AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  haveI := pullback_snd_isIso_of_range_subset f g H'
  inv (pullback.snd : pullback f g ⟶ _) ≫ pullback.fst
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift

@[simp, reassoc.1]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g :=
  by
  erw [Category.assoc]
  rw [IsIso.inv_comp_eq]
  exact pullback.condition
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_fac AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' := by rw [← cancel_mono f, hl, lift_fac]
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_uniq AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_uniq

theorem lift_range (H' : Set.range g.1.base ⊆ Set.range f.1.base) :
    Set.range (lift f g H').1.base = f.1.base ⁻¹' Set.range g.1.base :=
  by
  haveI := pullback_snd_isIso_of_range_subset f g H'
  dsimp only [lift]
  have : _ = (pullback.fst : pullback f g ⟶ _).val.base :=
    PreservesPullback.iso_hom_fst (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _)
      f g
  rw [LocallyRingedSpace.comp_val, SheafedSpace.comp_base, ← this, ← Category.assoc, coe_comp]
  rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ, TopCat.pullback_fst_range]
  ext
  constructor
  · rintro ⟨y, eq⟩
    exact ⟨y, eq.symm⟩
  · rintro ⟨y, eq⟩
    exact ⟨y, eq.symm⟩
  · rw [← TopCat.epi_iff_surjective]
    rw [show (inv (pullback.snd : pullback f g ⟶ _)).val.base = _ from
        (LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forget _).map_inv _]
    infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.lift_range AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_range

end Pullback

/-- An open immersion is isomorphic to the induced open subscheme on its image. -/
def isoRestrict {X Y : LocallyRingedSpace} {f : X ⟶ Y} (H : LocallyRingedSpace.IsOpenImmersion f) :
    X ≅ Y.restrict H.base_open :=
  by
  apply LocallyRingedSpace.isoOfSheafedSpaceIso
  refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
  exact H.iso_restrict
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.iso_restrict AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrict

/-- To show that a locally ringed space is a scheme, it suffices to show that it has a jointly
surjective family of open immersions from affine schemes. -/
protected def scheme (X : LocallyRingedSpace)
    (h :
      ∀ x : X,
        ∃ (R : CommRingCat)(f : Spec.toLocallyRingedSpace.obj (op R) ⟶ X),
          (x ∈ Set.range f.1.base : _) ∧ LocallyRingedSpace.IsOpenImmersion f) :
    Scheme where
  toLocallyRingedSpace := X
  local_affine := by
    intro x
    obtain ⟨R, f, h₁, h₂⟩ := h x
    refine' ⟨⟨⟨_, h₂.base_open.open_range⟩, h₁⟩, R, ⟨_⟩⟩
    apply LocallyRingedSpace.isoOfSheafedSpaceIso
    refine' SheafedSpace.forget_to_PresheafedSpace.preimage_iso _
    skip
    apply PresheafedSpace.IsOpenImmersion.isoOfRangeEq (PresheafedSpace.ofRestrict _ _) f.1
    · exact Subtype.range_coe_subtype
    · infer_instance
#align algebraic_geometry.LocallyRingedSpace.is_open_immersion.Scheme AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme

end LocallyRingedSpace.IsOpenImmersion

theorem IsOpenImmersion.open_range {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] :
    IsOpen (Set.range f.1.base) :=
  H.base_open.open_range
#align algebraic_geometry.is_open_immersion.open_range AlgebraicGeometry.IsOpenImmersion.open_range

section OpenCover

namespace Scheme

-- TODO: provide API to and from a presieve.
/-- An open cover of `X` consists of a family of open immersions into `X`,
and for each `x : X` an open immersion (indexed by `f x`) that covers `x`.

This is merely a coverage in the Zariski pretopology, and it would be optimal
if we could reuse the existing API about pretopologies, However, the definitions of sieves and
grothendieck topologies uses `Prop`s, so that the actual open sets and immersions are hard to
obtain. Also, since such a coverage in the pretopology usually contains a proper class of
immersions, it is quite hard to glue them, reason about finite covers, etc.
-/
structure OpenCover (X : Scheme.{u}) where
  J : Type v
  obj : ∀ j : J, Scheme
  map : ∀ j : J, obj j ⟶ X
  f : X.carrier → J
  Covers : ∀ x, x ∈ Set.range (map (f x)).1.base
  IsOpen : ∀ x, IsOpenImmersion (map x) := by infer_instance
#align algebraic_geometry.Scheme.open_cover AlgebraicGeometry.Scheme.OpenCover

attribute [instance] open_cover.is_open

variable {X Y Z : Scheme.{u}} (𝒰 : OpenCover X) (f : X ⟶ Z) (g : Y ⟶ Z)

variable [∀ x, HasPullback (𝒰.map x ≫ f) g]

/-- The affine cover of a scheme. -/
def affineCover (X : Scheme) : OpenCover X
    where
  J := X.carrier
  obj x := spec.obj <| Opposite.op (X.local_affine x).choose_spec.choose
  map x :=
    ((X.local_affine x).choose_spec.choose_spec.some.inv ≫ X.toLocallyRingedSpace.ofRestrict _ : _)
  f x := x
  IsOpen x :=
    by
    apply (config := { instances := false }) PresheafedSpace.IsOpenImmersion.comp
    infer_instance
    apply PresheafedSpace.IsOpenImmersion.ofRestrict
  Covers := by
    intro x
    erw [coe_comp]
    rw [Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ]
    erw [Subtype.range_coe_subtype]
    exact (X.local_affine x).choose.2
    rw [← TopCat.epi_iff_surjective]
    change Epi ((SheafedSpace.forget _).map (LocallyRingedSpace.forget_to_SheafedSpace.map _))
    infer_instance
#align algebraic_geometry.Scheme.affine_cover AlgebraicGeometry.Scheme.affineCover

instance : Inhabited X.OpenCover :=
  ⟨X.affineCover⟩

/-- Given an open cover `{ Uᵢ }` of `X`, and for each `Uᵢ` an open cover, we may combine these
open covers to form an open cover of `X`.  -/
@[simps J obj map]
def OpenCover.bind (f : ∀ x : 𝒰.J, OpenCover (𝒰.obj x)) : OpenCover X
    where
  J := Σi : 𝒰.J, (f i).J
  obj x := (f x.1).obj x.2
  map x := (f x.1).map x.2 ≫ 𝒰.map x.1
  f x := ⟨_, (f _).f (𝒰.covers x).choose⟩
  Covers x := by
    let y := (𝒰.covers x).choose
    have hy : (𝒰.map (𝒰.f x)).val.base y = x := (𝒰.covers x).choose_spec
    rcases(f (𝒰.f x)).covers y with ⟨z, hz⟩
    change x ∈ Set.range ((f (𝒰.f x)).map ((f (𝒰.f x)).f y) ≫ 𝒰.map (𝒰.f x)).1.base
    use z
    erw [comp_apply]
    rw [hz, hy]
#align algebraic_geometry.Scheme.open_cover.bind AlgebraicGeometry.Scheme.OpenCover.bind

/-- An isomorphism `X ⟶ Y` is an open cover of `Y`. -/
@[simps J obj map]
def openCoverOfIsIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] : OpenCover Y
    where
  J := PUnit.{v + 1}
  obj _ := X
  map _ := f
  f _ := PUnit.unit
  Covers x := by
    rw [set.range_iff_surjective.mpr]
    · trivial
    rw [← TopCat.epi_iff_surjective]
    infer_instance
#align algebraic_geometry.Scheme.open_cover_of_is_iso AlgebraicGeometry.Scheme.openCoverOfIsIso

/-- We construct an open cover from another, by providing the needed fields and showing that the
provided fields are isomorphic with the original open cover. -/
@[simps J obj map]
def OpenCover.copy {X : Scheme} (𝒰 : OpenCover X) (J : Type _) (obj : J → Scheme)
    (map : ∀ i, obj i ⟶ X) (e₁ : J ≃ 𝒰.J) (e₂ : ∀ i, obj i ≅ 𝒰.obj (e₁ i))
    (e₂ : ∀ i, map i = (e₂ i).hom ≫ 𝒰.map (e₁ i)) : OpenCover X :=
  { J
    obj
    map
    f := fun x => e₁.symm (𝒰.f x)
    Covers := fun x =>
      by
      rw [e₂, Scheme.comp_val_base, coe_comp, Set.range_comp, set.range_iff_surjective.mpr,
        Set.image_univ, e₁.right_inverse_symm]
      · exact 𝒰.covers x
      · rw [← TopCat.epi_iff_surjective]
        infer_instance
    IsOpen := fun i => by
      rw [e₂]
      infer_instance }
#align algebraic_geometry.Scheme.open_cover.copy AlgebraicGeometry.Scheme.OpenCover.copy

/-- The pushforward of an open cover along an isomorphism. -/
@[simps J obj map]
def OpenCover.pushforwardIso {X Y : Scheme} (𝒰 : OpenCover X) (f : X ⟶ Y) [IsIso f] : OpenCover Y :=
  ((openCoverOfIsIso f).bind fun _ => 𝒰).copy 𝒰.J _ _
    ((Equiv.punitProd _).symm.trans (Equiv.sigmaEquivProd PUnit 𝒰.J).symm) (fun _ => Iso.refl _)
    fun _ => (Category.id_comp _).symm
#align algebraic_geometry.Scheme.open_cover.pushforward_iso AlgebraicGeometry.Scheme.OpenCover.pushforwardIso

/-- Adding an open immersion into an open cover gives another open cover. -/
@[simps]
def OpenCover.add {X : Scheme} (𝒰 : X.OpenCover) {Y : Scheme} (f : Y ⟶ X) [IsOpenImmersion f] :
    X.OpenCover where
  J := Option 𝒰.J
  obj i := Option.rec Y 𝒰.obj i
  map i := Option.rec f 𝒰.map i
  f x := some (𝒰.f x)
  Covers := 𝒰.covers
  IsOpen := by rintro (_ | _) <;> dsimp <;> infer_instance
#align algebraic_geometry.Scheme.open_cover.add AlgebraicGeometry.Scheme.OpenCover.add

-- Related result : `open_cover.pullback_cover`, where we pullback an open cover on `X` along a
-- morphism `W ⟶ X`. This is provided at the end of the file since it needs some more results
-- about open immersion (which in turn needs the open cover API).
attribute [local reducible] CommRingCat.of CommRingCat.ofHom

instance val_base_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] : IsIso f.1.base :=
  Scheme.forgetToTop.map_isIso f
#align algebraic_geometry.Scheme.val_base_is_iso AlgebraicGeometry.Scheme.val_base_isIso

instance basic_open_isOpenImmersion {R : CommRingCat} (f : R) :
    AlgebraicGeometry.IsOpenImmersion
      (Scheme.spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away f))).op) :=
  by
  apply (config := { instances := false }) SheafedSpace.IsOpenImmersion.of_stalk_iso
  any_goals infer_instance
  any_goals infer_instance
  exact (PrimeSpectrum.localization_away_openEmbedding (Localization.Away f) f : _)
  intro x
  exact Spec_map_localization_isIso R (Submonoid.powers f) x
#align algebraic_geometry.Scheme.basic_open_is_open_immersion AlgebraicGeometry.Scheme.basic_open_isOpenImmersion

/-- The basic open sets form an affine open cover of `Spec R`. -/
def affineBasisCoverOfAffine (R : CommRingCat) : OpenCover (spec.obj (Opposite.op R))
    where
  J := R
  obj r := spec.obj (Opposite.op <| CommRingCat.of <| Localization.Away r)
  map r := spec.map (Quiver.Hom.op (algebraMap R (Localization.Away r) : _))
  f x := 1
  Covers r := by
    rw [set.range_iff_surjective.mpr ((TopCat.epi_iff_surjective _).mp _)]
    · exact trivial
    · infer_instance
  IsOpen x := AlgebraicGeometry.Scheme.basic_open_isOpenImmersion x
#align algebraic_geometry.Scheme.affine_basis_cover_of_affine AlgebraicGeometry.Scheme.affineBasisCoverOfAffine

/-- We may bind the basic open sets of an open affine cover to form a affine cover that is also
a basis. -/
def affineBasisCover (X : Scheme) : OpenCover X :=
  X.affineCover.bind fun x => affineBasisCoverOfAffine _
#align algebraic_geometry.Scheme.affine_basis_cover AlgebraicGeometry.Scheme.affineBasisCover

/-- The coordinate ring of a component in the `affine_basis_cover`. -/
def affineBasisCoverRing (X : Scheme) (i : X.affineBasisCover.J) : CommRingCat :=
  CommRingCat.of <| @Localization.Away (X.local_affine i.1).choose_spec.choose _ i.2
#align algebraic_geometry.Scheme.affine_basis_cover_ring AlgebraicGeometry.Scheme.affineBasisCoverRing

theorem affineBasisCover_obj (X : Scheme) (i : X.affineBasisCover.J) :
    X.affineBasisCover.obj i = spec.obj (op <| X.affineBasisCoverRing i) :=
  rfl
#align algebraic_geometry.Scheme.affine_basis_cover_obj AlgebraicGeometry.Scheme.affineBasisCover_obj

theorem affineBasisCover_map_range (X : Scheme) (x : X.carrier)
    (r : (X.local_affine x).choose_spec.choose) :
    Set.range (X.affineBasisCover.map ⟨x, r⟩).1.base =
      (X.affineCover.map x).1.base '' (PrimeSpectrum.basicOpen r).1 :=
  by
  erw [coe_comp, Set.range_comp]
  congr
  exact (PrimeSpectrum.localization_away_comap_range (Localization.Away r) r : _)
#align algebraic_geometry.Scheme.affine_basis_cover_map_range AlgebraicGeometry.Scheme.affineBasisCover_map_range

theorem affineBasisCover_is_basis (X : Scheme) :
    TopologicalSpace.IsTopologicalBasis
      { x : Set X.carrier |
        ∃ a : X.affineBasisCover.J, x = Set.range (X.affineBasisCover.map a).1.base } :=
  by
  apply TopologicalSpace.isTopologicalBasis_of_open_of_nhds
  · rintro _ ⟨a, rfl⟩
    exact IsOpenImmersion.open_range (X.affine_basis_cover.map a)
  · rintro a U haU hU
    rcases X.affine_cover.covers a with ⟨x, e⟩
    let U' := (X.affine_cover.map (X.affine_cover.f a)).1.base ⁻¹' U
    have hxU' : x ∈ U' := by
      rw [← e] at haU
      exact haU
    rcases prime_spectrum.is_basis_basic_opens.exists_subset_of_mem_open hxU'
        ((X.affine_cover.map (X.affine_cover.f a)).1.base.continuous_toFun.isOpen_preimage _
          hU) with
      ⟨_, ⟨_, ⟨s, rfl⟩, rfl⟩, hxV, hVU⟩
    refine' ⟨_, ⟨⟨_, s⟩, rfl⟩, _, _⟩ <;> erw [affineBasisCover_map_range]
    · exact ⟨x, hxV, e⟩
    · rw [Set.image_subset_iff]
      exact hVU
#align algebraic_geometry.Scheme.affine_basis_cover_is_basis AlgebraicGeometry.Scheme.affineBasisCover_is_basis

/-- Every open cover of a quasi-compact scheme can be refined into a finite subcover.
-/
@[simps obj map]
def OpenCover.finiteSubcover {X : Scheme} (𝒰 : OpenCover X) [H : CompactSpace X.carrier] :
    OpenCover X :=
  by
  have :=
    @compact_space.elim_nhds_subcover _ H (fun x : X.carrier => Set.range (𝒰.map (𝒰.f x)).1.base)
      fun x => (IsOpenImmersion.open_range (𝒰.map (𝒰.f x))).mem_nhds (𝒰.covers x)
  let t := this.some
  have h : ∀ x : X.carrier, ∃ y : t, x ∈ Set.range (𝒰.map (𝒰.f y)).1.base :=
    by
    intro x
    have h' : x ∈ (⊤ : Set X.carrier) := trivial
    rw [← Classical.choose_spec this, Set.mem_unionᵢ] at h'
    rcases h' with ⟨y, _, ⟨hy, rfl⟩, hy'⟩
    exact ⟨⟨y, hy⟩, hy'⟩
  exact
    { J := t
      obj := fun x => 𝒰.obj (𝒰.f x.1)
      map := fun x => 𝒰.map (𝒰.f x.1)
      f := fun x => (h x).choose
      Covers := fun x => (h x).choose_spec }
#align algebraic_geometry.Scheme.open_cover.finite_subcover AlgebraicGeometry.Scheme.OpenCover.finiteSubcover

instance [H : CompactSpace X.carrier] : Fintype 𝒰.finiteSubcover.J :=
  by
  delta open_cover.finite_subcover
  infer_instance

end Scheme

end OpenCover

namespace PresheafedSpace.IsOpenImmersion

section ToScheme

variable {X : PresheafedSpace.{u} CommRingCat.{u}} (Y : Scheme.{u})

variable (f : X ⟶ Y.toPresheafedSpace) [H : PresheafedSpace.IsOpenImmersion f]

include H

/-- If `X ⟶ Y` is an open immersion, and `Y` is a scheme, then so is `X`. -/
def toScheme : Scheme :=
  by
  apply LocallyRingedSpace.IsOpenImmersion.scheme (toLocallyRingedSpace _ f)
  intro x
  obtain ⟨_, ⟨i, rfl⟩, hx, hi⟩ :=
    Y.affine_basis_cover_is_basis.exists_subset_of_mem_open (Set.mem_range_self x)
      H.base_open.open_range
  use Y.affine_basis_cover_ring i
  use LocallyRingedSpace.IsOpenImmersion.lift (toLocallyRingedSpaceHom _ f) _ hi
  constructor
  · rw [LocallyRingedSpace.IsOpenImmersion.lift_range]
    exact hx
  · delta LocallyRingedSpace.is_open_immersion.lift
    infer_instance
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toScheme

@[simp]
theorem toScheme_toLocallyRingedSpace :
    (toScheme Y f).toLocallyRingedSpace = toLocallyRingedSpace Y.1 f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_to_LocallyRingedSpace AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toScheme_toLocallyRingedSpace

/-- If `X ⟶ Y` is an open immersion of PresheafedSpaces, and `Y` is a Scheme, we can
upgrade it into a morphism of Schemes.
-/
def toSchemeHom : toScheme Y f ⟶ Y :=
  toLocallyRingedSpaceHom _ f
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSchemeHom

@[simp]
theorem toSchemeHom_val : (toSchemeHom Y f).val = f :=
  rfl
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom_val AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSchemeHom_val

instance toSchemeHom_isOpenImmersion : IsOpenImmersion (toSchemeHom Y f) :=
  H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.to_Scheme_hom_is_open_immersion AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.toSchemeHom_isOpenImmersion

omit H

theorem scheme_eq_of_locallyRingedSpace_eq {X Y : Scheme}
    (H : X.toLocallyRingedSpace = Y.toLocallyRingedSpace) : X = Y :=
  by
  cases X
  cases Y
  congr
  exact H
#align algebraic_geometry.PresheafedSpace.is_open_immersion.Scheme_eq_of_LocallyRingedSpace_eq AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.scheme_eq_of_locallyRingedSpace_eq

theorem scheme_toScheme {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : toScheme Y f.1 = X :=
  by
  apply scheme_eq_of_locallyRingedSpace_eq
  exact locallyRingedSpace_toLocallyRingedSpace f
#align algebraic_geometry.PresheafedSpace.is_open_immersion.Scheme_to_Scheme AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.scheme_toScheme

end ToScheme

end PresheafedSpace.IsOpenImmersion

/-- The restriction of a Scheme along an open embedding. -/
@[simps]
def Scheme.restrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X.carrier} (h : OpenEmbedding f) :
    Scheme :=
  { PresheafedSpace.IsOpenImmersion.toScheme X (X.toPresheafedSpace.ofRestrict h) with
    toPresheafedSpace := X.toPresheafedSpace.restrict h }
#align algebraic_geometry.Scheme.restrict AlgebraicGeometry.Scheme.restrict

/-- The canonical map from the restriction to the supspace. -/
@[simps]
def Scheme.ofRestrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X.carrier}
    (h : OpenEmbedding f) : X.restrict h ⟶ X :=
  X.toLocallyRingedSpace.ofRestrict h
#align algebraic_geometry.Scheme.of_restrict AlgebraicGeometry.Scheme.ofRestrict

instance IsOpenImmersion.ofRestrict {U : TopCat} (X : Scheme) {f : U ⟶ TopCat.of X.carrier}
    (h : OpenEmbedding f) : IsOpenImmersion (X.ofRestrict h) :=
  show PresheafedSpace.IsOpenImmersion (X.toPresheafedSpace.ofRestrict h) by infer_instance
#align algebraic_geometry.is_open_immersion.of_restrict AlgebraicGeometry.IsOpenImmersion.ofRestrict

namespace IsOpenImmersion

variable {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

variable [H : IsOpenImmersion f]

instance (priority := 100) of_isIso [IsIso g] : IsOpenImmersion g :=
  @LocallyRingedSpace.IsOpenImmersion.of_isIso _
    (show IsIso ((inducedFunctor _).map g) by infer_instance)
#align algebraic_geometry.is_open_immersion.of_is_iso AlgebraicGeometry.IsOpenImmersion.of_isIso

theorem to_iso {X Y : Scheme} (f : X ⟶ Y) [h : IsOpenImmersion f] [Epi f.1.base] : IsIso f :=
  @isIso_of_reflects_iso _ _ f
    (Scheme.forgetToLocallyRingedSpace ⋙
      LocallyRingedSpace.forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace)
    (@PresheafedSpace.IsOpenImmersion.to_iso _ f.1 h _) _
#align algebraic_geometry.is_open_immersion.to_iso AlgebraicGeometry.IsOpenImmersion.to_iso

theorem of_stalk_iso {X Y : Scheme} (f : X ⟶ Y) (hf : OpenEmbedding f.1.base)
    [∀ x, IsIso (PresheafedSpace.stalkMap f.1 x)] : IsOpenImmersion f :=
  SheafedSpace.IsOpenImmersion.of_stalk_iso f.1 hf
#align algebraic_geometry.is_open_immersion.of_stalk_iso AlgebraicGeometry.IsOpenImmersion.of_stalk_iso

theorem iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ OpenEmbedding f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) :=
  ⟨fun H => ⟨H.1, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.of_stalk_iso f h₁ h₂⟩
#align algebraic_geometry.is_open_immersion.iff_stalk_iso AlgebraicGeometry.IsOpenImmersion.iff_stalk_iso

theorem AlgebraicGeometry.isIso_iff_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) :
    IsIso f ↔ IsOpenImmersion f ∧ Epi f.1.base :=
  ⟨fun H => ⟨inferInstance, inferInstance⟩, fun ⟨h₁, h₂⟩ => @IsOpenImmersion.to_iso f h₁ h₂⟩
#align algebraic_geometry.is_iso_iff_is_open_immersion AlgebraicGeometry.isIso_iff_isOpenImmersion

theorem AlgebraicGeometry.isIso_iff_stalk_iso {X Y : Scheme} (f : X ⟶ Y) :
    IsIso f ↔ IsIso f.1.base ∧ ∀ x, IsIso (PresheafedSpace.stalkMap f.1 x) :=
  by
  rw [isIso_iff_isOpenImmersion, IsOpenImmersion.iff_stalk_iso, and_comm', ← and_assoc']
  refine' and_congr ⟨_, _⟩ Iff.rfl
  · rintro ⟨h₁, h₂⟩
    convert_to
      IsIso
        (TopCat.isoOfHomeo
            (Homeomorph.homeomorphOfContinuousOpen
              (Equiv.ofBijective _ ⟨h₂.inj, (TopCat.epi_iff_surjective _).mp h₁⟩) h₂.continuous
              h₂.is_open_map)).hom
    · ext
      rfl
    · infer_instance
  · intro H
    exact ⟨inferInstance, (TopCat.homeoOfIso (asIso f.1.base)).openEmbedding⟩
#align algebraic_geometry.is_iso_iff_stalk_iso AlgebraicGeometry.isIso_iff_stalk_iso

/-- A open immersion induces an isomorphism from the domain onto the image -/
def isoRestrict : X ≅ (Z.restrict H.base_open : _) :=
  ⟨H.isoRestrict.hom, H.isoRestrict.inv, H.isoRestrict.hom_inv_id, H.isoRestrict.inv_hom_id⟩
#align algebraic_geometry.is_open_immersion.iso_restrict AlgebraicGeometry.IsOpenImmersion.isoRestrict

include H

-- mathport name: exprforget
local notation "forget" => Scheme.forgetToLocallyRingedSpace

instance mono : Mono f :=
  (inducedFunctor _).mono_of_mono_map (show @Mono LocallyRingedSpace _ _ _ f by infer_instance)
#align algebraic_geometry.is_open_immersion.mono AlgebraicGeometry.IsOpenImmersion.mono

instance forget_map_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (forget.map f) :=
  ⟨H.base_open, H.c_iso⟩
#align algebraic_geometry.is_open_immersion.forget_map_is_open_immersion AlgebraicGeometry.IsOpenImmersion.forget_map_isOpenImmersion

instance hasLimitCospanForgetOfLeft : HasLimit (cospan f g ⋙ Scheme.forgetToLocallyRingedSpace) :=
  by
  apply hasLimitOfIso (diagramIsoCospan.{u} _).symm
  change HasLimit (cospan (forget.map f) (forget.map g))
  infer_instance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_left AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfLeft

open CategoryTheory.Limits.WalkingCospan

instance hasLimitCospanForgetOfLeft' :
    HasLimit (cospan ((cospan f g ⋙ forget).map Hom.inl) ((cospan f g ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map f) (forget.map g)) from inferInstance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_left' AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfLeft'

instance hasLimitCospanForgetOfRight : HasLimit (cospan g f ⋙ forget) :=
  by
  apply hasLimitOfIso (diagramIsoCospan.{u} _).symm
  change HasLimit (cospan (forget.map g) (forget.map f))
  infer_instance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_right AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfRight

instance hasLimitCospanForgetOfRight' :
    HasLimit (cospan ((cospan g f ⋙ forget).map Hom.inl) ((cospan g f ⋙ forget).map Hom.inr)) :=
  show HasLimit (cospan (forget.map g) (forget.map f)) from inferInstance
#align algebraic_geometry.is_open_immersion.has_limit_cospan_forget_of_right' AlgebraicGeometry.IsOpenImmersion.hasLimitCospanForgetOfRight'

instance forgetCreatesPullbackOfLeft : CreatesLimit (cospan f g) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.snd LocallyRingedSpace _ _ _ _ f g _).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.is_open_immersion.forget_creates_pullback_of_left AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfLeft

instance forgetCreatesPullbackOfRight : CreatesLimit (cospan g f) forget :=
  createsLimitOfFullyFaithfulOfIso
    (PresheafedSpace.IsOpenImmersion.toScheme Y (@pullback.fst LocallyRingedSpace _ _ _ _ g f _).1)
    (eqToIso (by simp) ≪≫ HasLimit.isoOfNatIso (diagramIsoCospan _).symm)
#align algebraic_geometry.is_open_immersion.forget_creates_pullback_of_right AlgebraicGeometry.IsOpenImmersion.forgetCreatesPullbackOfRight

instance forgetPreservesOfLeft : PreservesLimit (cospan f g) forget :=
  CategoryTheory.preservesLimitOfCreatesLimitAndHasLimit _ _
#align algebraic_geometry.is_open_immersion.forget_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfLeft

instance forgetPreservesOfRight : PreservesLimit (cospan g f) forget :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.is_open_immersion.forget_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetPreservesOfRight

instance hasPullback_of_left : HasPullback f g :=
  hasLimitOfCreated (cospan f g) forget
#align algebraic_geometry.is_open_immersion.has_pullback_of_left AlgebraicGeometry.IsOpenImmersion.hasPullback_of_left

instance hasPullback_of_right : HasPullback g f :=
  hasLimitOfCreated (cospan g f) forget
#align algebraic_geometry.is_open_immersion.has_pullback_of_right AlgebraicGeometry.IsOpenImmersion.hasPullback_of_right

instance pullback_snd_of_left : IsOpenImmersion (pullback.snd : pullback f g ⟶ _) :=
  by
  have := PreservesPullback.iso_hom_snd forget f g
  dsimp only [Scheme.forgetToLocallyRingedSpace, inducedFunctor_map] at this
  rw [← this]
  change LocallyRingedSpace.IsOpenImmersion _
  infer_instance
#align algebraic_geometry.is_open_immersion.pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.pullback_snd_of_left

instance pullback_fst_of_right : IsOpenImmersion (pullback.fst : pullback g f ⟶ _) :=
  by
  rw [← pullbackSymmetry_hom_comp_snd]
  infer_instance
#align algebraic_geometry.is_open_immersion.pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.pullback_fst_of_right

instance pullback_to_base [IsOpenImmersion g] :
    IsOpenImmersion (limit.π (cospan f g) WalkingCospan.one) :=
  by
  rw [← limit.w (cospan f g) WalkingCospan.Hom.inl]
  change IsOpenImmersion (_ ≫ f)
  infer_instance
#align algebraic_geometry.is_open_immersion.pullback_to_base AlgebraicGeometry.IsOpenImmersion.pullback_to_base

instance forgetToTopPreservesOfLeft : PreservesLimit (cospan f g) Scheme.forgetToTop :=
  by
  apply (config := { instances := false }) Limits.compPreservesLimit
  infer_instance
  apply preservesLimitOfIsoDiagram _ (diagramIsoCospan.{u} _).symm
  dsimp [LocallyRingedSpace.forgetToTop]
  infer_instance
#align algebraic_geometry.is_open_immersion.forget_to_Top_preserves_of_left AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfLeft

instance forgetToTopPreservesOfRight : PreservesLimit (cospan g f) Scheme.forgetToTop :=
  preservesPullbackSymmetry _ _ _
#align algebraic_geometry.is_open_immersion.forget_to_Top_preserves_of_right AlgebraicGeometry.IsOpenImmersion.forgetToTopPreservesOfRight

theorem range_pullback_snd_of_left :
    Set.range (pullback.snd : pullback f g ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [←
    show _ = (pullback.snd : pullback f g ⟶ _).1.base from
      PreservesPullback.iso_hom_snd Scheme.forgetToTop f g,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @set.preimage_univ _ _ (pullback.fst : pullback f.1.base g.1.base ⟶ _),
    TopCat.pullback_snd_image_fst_preimage, Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.is_open_immersion.range_pullback_snd_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_snd_of_left

theorem range_pullback_fst_of_right :
    Set.range (pullback.fst : pullback g f ⟶ Y).1.base =
      (Opens.map g.1.base).obj ⟨Set.range f.1.base, H.base_open.open_range⟩ :=
  by
  rw [←
    show _ = (pullback.fst : pullback g f ⟶ _).1.base from
      PreservesPullback.iso_hom_fst Scheme.forgetToTop g f,
    coe_comp, Set.range_comp, set.range_iff_surjective.mpr, ←
    @set.preimage_univ _ _ (pullback.snd : pullback g.1.base f.1.base ⟶ _),
    TopCat.pullback_fst_image_snd_preimage, Set.image_univ]
  rfl
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.is_open_immersion.range_pullback_fst_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_fst_of_right

theorem range_pullback_to_base_of_left :
    Set.range (pullback.fst ≫ f : pullback f g ⟶ Z).1.base =
      Set.range f.1.base ∩ Set.range g.1.base :=
  by
  rw [pullback.condition, Scheme.comp_val_base, coe_comp, Set.range_comp,
    range_pullback_snd_of_left, Opens.map_obj, Subtype.coe_mk, Set.image_preimage_eq_inter_range,
    Set.inter_comm]
#align algebraic_geometry.is_open_immersion.range_pullback_to_base_of_left AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_left

theorem range_pullback_to_base_of_right :
    Set.range (pullback.fst ≫ g : pullback g f ⟶ Z).1.base =
      Set.range g.1.base ∩ Set.range f.1.base :=
  by
  rw [Scheme.comp_val_base, coe_comp, Set.range_comp, range_pullback_fst_of_right, Opens.map_obj,
    Subtype.coe_mk, Set.image_preimage_eq_inter_range, Set.inter_comm]
#align algebraic_geometry.is_open_immersion.range_pullback_to_base_of_right AlgebraicGeometry.IsOpenImmersion.range_pullback_to_base_of_right

/-- The universal property of open immersions:
For an open immersion `f : X ⟶ Z`, given any morphism of schemes `g : Y ⟶ Z` whose topological
image is contained in the image of `f`, we can lift this morphism to a unique `Y ⟶ X` that
commutes with these maps.
-/
def lift (H' : Set.range g.1.base ⊆ Set.range f.1.base) : Y ⟶ X :=
  LocallyRingedSpace.IsOpenImmersion.lift f g H'
#align algebraic_geometry.is_open_immersion.lift AlgebraicGeometry.IsOpenImmersion.lift

@[simp, reassoc.1]
theorem lift_fac (H' : Set.range g.1.base ⊆ Set.range f.1.base) : lift f g H' ≫ f = g :=
  LocallyRingedSpace.IsOpenImmersion.lift_fac f g H'
#align algebraic_geometry.is_open_immersion.lift_fac AlgebraicGeometry.IsOpenImmersion.lift_fac

theorem lift_uniq (H' : Set.range g.1.base ⊆ Set.range f.1.base) (l : Y ⟶ X) (hl : l ≫ f = g) :
    l = lift f g H' :=
  LocallyRingedSpace.IsOpenImmersion.lift_uniq f g H' l hl
#align algebraic_geometry.is_open_immersion.lift_uniq AlgebraicGeometry.IsOpenImmersion.lift_uniq

/-- Two open immersions with equal range are isomorphic. -/
@[simps]
def isoOfRangeEq [IsOpenImmersion g] (e : Set.range f.1.base = Set.range g.1.base) : X ≅ Y
    where
  Hom := lift g f (le_of_eq e)
  inv := lift f g (le_of_eq e.symm)
  hom_inv_id' := by
    rw [← cancel_mono f]
    simp
  inv_hom_id' := by
    rw [← cancel_mono g]
    simp
#align algebraic_geometry.is_open_immersion.iso_of_range_eq AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq

/-- The functor `opens X ⥤ opens Y` associated with an open immersion `f : X ⟶ Y`. -/
abbrev AlgebraicGeometry.Scheme.Hom.opensFunctor {X Y : Scheme} (f : X ⟶ Y)
    [H : IsOpenImmersion f] : Opens X.carrier ⥤ Opens Y.carrier :=
  H.openFunctor
#align algebraic_geometry.Scheme.hom.opens_functor AlgebraicGeometry.Scheme.Hom.opensFunctor

/-- The isomorphism `Γ(X, U) ⟶ Γ(Y, f(U))` induced by an open immersion `f : X ⟶ Y`. -/
def AlgebraicGeometry.Scheme.Hom.invApp {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] (U) :
    X.presheaf.obj (op U) ⟶ Y.presheaf.obj (op (f.opensFunctor.obj U)) :=
  H.invApp U
#align algebraic_geometry.Scheme.hom.inv_app AlgebraicGeometry.Scheme.Hom.invApp

theorem app_eq_inv_app_app_of_comp_eq_aux {X Y U : Scheme} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U.carrier) :
    (Opens.map f.1.base).obj V = (Opens.map fg.1.base).obj (g.opensFunctor.obj V) :=
  by
  subst H
  rw [Scheme.comp_val_base, Opens.map_comp_obj]
  congr 1
  ext1
  exact (Set.preimage_image_eq _ h.base_open.inj).symm
#align algebraic_geometry.is_open_immersion.app_eq_inv_app_app_of_comp_eq_aux AlgebraicGeometry.IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux

/-- The `fg` argument is to avoid nasty stuff about dependent types. -/
theorem app_eq_invApp_app_of_comp_eq {X Y U : Scheme} (f : Y ⟶ U) (g : U ⟶ X) (fg : Y ⟶ X)
    (H : fg = f ≫ g) [h : IsOpenImmersion g] (V : Opens U.carrier) :
    f.1.c.app (op V) =
      g.invApp _ ≫
        fg.1.c.app _ ≫
          Y.presheaf.map
            (eqToHom <| IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux f g fg H V).op :=
  by
  subst H
  rw [Scheme.comp_val_c_app, Category.assoc, Scheme.Hom.invApp,
    PresheafedSpace.IsOpenImmersion.invApp_app_assoc, f.val.c.naturality_assoc,
    TopCat.Presheaf.pushforwardObj_map, ← Functor.map_comp]
  convert (Category.comp_id _).symm
  convert Y.presheaf.map_id _
#align algebraic_geometry.is_open_immersion.app_eq_inv_app_app_of_comp_eq AlgebraicGeometry.IsOpenImmersion.app_eq_invApp_app_of_comp_eq

theorem lift_app {X Y U : Scheme} (f : U ⟶ Y) (g : X ⟶ Y) [h : IsOpenImmersion f] (H)
    (V : Opens U.carrier) :
    (IsOpenImmersion.lift f g H).1.c.app (op V) =
      f.invApp _ ≫
        g.1.c.app _ ≫
          X.presheaf.map
            (eqToHom <|
                IsOpenImmersion.app_eq_inv_app_app_of_comp_eq_aux _ _ _
                  (IsOpenImmersion.lift_fac f g H).symm V).op :=
  IsOpenImmersion.app_eq_invApp_app_of_comp_eq _ _ _ _ _
#align algebraic_geometry.is_open_immersion.lift_app AlgebraicGeometry.IsOpenImmersion.lift_app

end IsOpenImmersion

namespace Scheme

theorem image_basicOpen {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] {U : Opens X.carrier}
    (r : X.presheaf.obj (op U)) : f.opensFunctor.obj (X.basicOpen r) = Y.basicOpen (f.invApp U r) :=
  by
  have e := Scheme.preimage_basicOpen f (f.inv_app U r)
  rw [Scheme.Hom.invApp, PresheafedSpace.IsOpenImmersion.invApp_app_apply, Scheme.basicOpen_res,
    inf_eq_right.mpr _] at e
  rw [← e]
  ext1
  refine' set.image_preimage_eq_inter_range.trans _
  erw [Set.inter_eq_left_iff_subset]
  refine' Set.Subset.trans (Scheme.basicOpen_le _ _) (Set.image_subset_range _ _)
  refine' le_trans (Scheme.basicOpen_le _ _) (le_of_eq _)
  ext1
  exact (Set.preimage_image_eq _ H.base_open.inj).symm
#align algebraic_geometry.Scheme.image_basic_open AlgebraicGeometry.Scheme.image_basicOpen

/-- The image of an open immersion as an open set. -/
@[simps]
def Hom.opensRange {X Y : Scheme} (f : X ⟶ Y) [H : IsOpenImmersion f] : Opens Y.carrier :=
  ⟨_, H.base_open.open_range⟩
#align algebraic_geometry.Scheme.hom.opens_range AlgebraicGeometry.Scheme.Hom.opensRange

end Scheme

section

variable (X : Scheme)

/-- The functor taking open subsets of `X` to open subschemes of `X`. -/
@[simps obj_left obj_hom mapLeft]
def Scheme.restrictFunctor : Opens X.carrier ⥤ Over X
    where
  obj U := Over.mk (X.ofRestrict U.openEmbedding)
  map U V i :=
    Over.homMk
      (IsOpenImmersion.lift (X.ofRestrict _) (X.ofRestrict _)
        (by
          change Set.range coe ⊆ Set.range coe
          simp_rw [Subtype.range_coe]
          exact i.le))
      (IsOpenImmersion.lift_fac _ _ _)
  map_id' U := by
    ext1
    dsimp only [Over.homMk_left, Over.id_left]
    rw [← cancel_mono (X.of_restrict U.open_embedding), Category.id_comp, IsOpenImmersion.lift_fac]
  map_comp' U V W i j := by
    ext1
    dsimp only [Over.homMk_left, Over.comp_left]
    rw [← cancel_mono (X.of_restrict W.open_embedding), Category.assoc]
    iterate 3 rw [IsOpenImmersion.lift_fac]
#align algebraic_geometry.Scheme.restrict_functor AlgebraicGeometry.Scheme.restrictFunctor

@[reassoc.1]
theorem Scheme.restrictFunctor_map_ofRestrict {U V : Opens X.carrier} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1 ≫ X.ofRestrict _ = X.ofRestrict _ :=
  IsOpenImmersion.lift_fac _ _ _
#align algebraic_geometry.Scheme.restrict_functor_map_of_restrict AlgebraicGeometry.Scheme.restrictFunctor_map_ofRestrict

theorem Scheme.restrictFunctor_map_base {U V : Opens X.carrier} (i : U ⟶ V) :
    (X.restrictFunctor.map i).1.1.base = (Opens.toTop _).map i :=
  by
  ext a
  exact
    (congr_arg (fun f : X.restrict U.open_embedding ⟶ X => f.1.base a)
        (X.restrict_functor_map_of_restrict i) :
      _)
#align algebraic_geometry.Scheme.restrict_functor_map_base AlgebraicGeometry.Scheme.restrictFunctor_map_base

theorem Scheme.restrictFunctor_map_app_aux {U V : Opens X.carrier} (i : U ⟶ V) (W : Opens V) :
    U.openEmbedding.isOpenMap.functor.obj ((Opens.map (X.restrictFunctor.map i).1.val.base).obj W) ≤
      V.openEmbedding.isOpenMap.functor.obj W :=
  by
  simp only [set.image_congr, Subtype.mk_le_mk, IsOpenMap.functor, Set.image_subset_iff,
    Scheme.restrictFunctor_map_base, Opens.map, Subtype.coe_mk, Opens.inclusion_apply,
    Set.le_eq_subset]
  rintro _ h
  exact ⟨_, h, rfl⟩
#align algebraic_geometry.Scheme.restrict_functor_map_app_aux AlgebraicGeometry.Scheme.restrictFunctor_map_app_aux

theorem Scheme.restrictFunctor_map_app {U V : Opens X.carrier} (i : U ⟶ V) (W : Opens V) :
    (X.restrictFunctor.map i).1.1.c.app (op W) =
      X.presheaf.map (homOfLe <| X.restrictFunctor_map_app_aux i W).op :=
  by
  have e₁ :=
    Scheme.congr_app (X.restrict_functor_map_of_restrict i)
      (op <| V.open_embedding.is_open_map.functor.obj W)
  rw [Scheme.comp_val_c_app] at e₁
  have e₂ := (X.restrict_functor.map i).1.val.c.naturality (eqToHom W.map_functor_eq).op
  rw [← IsIso.eq_inv_comp] at e₂
  dsimp at e₁ e₂⊢
  rw [e₂, W.adjunction_counit_map_functor, ← IsIso.eq_inv_comp, IsIso.inv_comp_eq, ←
    IsIso.eq_comp_inv] at e₁
  simp_rw [eqToHom_map (Opens.map _), eqToHom_map (IsOpenMap.functor _), ← Functor.map_inv, ←
    Functor.map_comp] at e₁
  rw [e₁]
  congr 1
#align algebraic_geometry.Scheme.restrict_functor_map_app AlgebraicGeometry.Scheme.restrictFunctor_map_app

/-- The functor that restricts to open subschemes and then takes global section is
isomorphic to the structure sheaf. -/
@[simps]
def Scheme.restrictFunctorΓ : X.restrictFunctor.op ⋙ (Over.forget X).op ⋙ Scheme.Γ ≅ X.presheaf :=
  NatIso.ofComponents
    (fun U => X.presheaf.mapIso ((eqToIso (unop U).openEmbedding_obj_top).symm.op : _))
    (by
      intro U V i
      dsimp [-Subtype.val_eq_coe, -Scheme.restrict_functor_map_left]
      rw [X.restrict_functor_map_app, ← Functor.map_comp, ← Functor.map_comp]
      congr 1)
#align algebraic_geometry.Scheme.restrict_functor_Γ AlgebraicGeometry.Scheme.restrictFunctorΓ

end

/-- The restriction of an isomorphism onto an open set. -/
noncomputable abbrev Scheme.restrictMapIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f]
    (U : Opens Y.carrier) :
    X.restrict ((Opens.map f.1.base).obj U).openEmbedding ≅ Y.restrict U.openEmbedding :=
  by
  refine' IsOpenImmersion.isoOfRangeEq (X.of_restrict _ ≫ f) (Y.of_restrict _) _
  dsimp [Opens.inclusion]
  rw [coe_comp, Set.range_comp]
  dsimp
  rw [Subtype.range_coe, Subtype.range_coe]
  refine' @set.image_preimage_eq _ _ f.1.base U.1 _
  rw [← TopCat.epi_iff_surjective]
  infer_instance
#align algebraic_geometry.Scheme.restrict_map_iso AlgebraicGeometry.Scheme.restrictMapIso

/-- Given an open cover on `X`, we may pull them back along a morphism `W ⟶ X` to obtain
an open cover of `W`. -/
@[simps]
def Scheme.OpenCover.pullbackCover {X : Scheme} (𝒰 : X.OpenCover) {W : Scheme} (f : W ⟶ X) :
    W.OpenCover where
  J := 𝒰.J
  obj x := pullback f (𝒰.map x)
  map x := pullback.fst
  f x := 𝒰.f (f.1.base x)
  Covers x :=
    by
    rw [←
      show _ = (pullback.fst : pullback f (𝒰.map (𝒰.f (f.1.base x))) ⟶ _).1.base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f (𝒰.map (𝒰.f (f.1.base x)))]
    rw [coe_comp, Set.range_comp, set.range_iff_surjective.mpr, Set.image_univ,
      TopCat.pullback_fst_range]
    obtain ⟨y, h⟩ := 𝒰.covers (f.1.base x)
    exact ⟨y, h.symm⟩
    · rw [← TopCat.epi_iff_surjective]
      infer_instance
#align algebraic_geometry.Scheme.open_cover.pullback_cover AlgebraicGeometry.Scheme.OpenCover.pullbackCover

theorem Scheme.OpenCover.unionᵢ_range {X : Scheme} (𝒰 : X.OpenCover) :
    (⋃ i, Set.range (𝒰.map i).1.base) = Set.univ :=
  by
  rw [Set.eq_univ_iff_forall]
  intro x
  rw [Set.mem_unionᵢ]
  exact ⟨𝒰.f x, 𝒰.covers x⟩
#align algebraic_geometry.Scheme.open_cover.Union_range AlgebraicGeometry.Scheme.OpenCover.unionᵢ_range

theorem Scheme.OpenCover.supᵢ_opensRange {X : Scheme} (𝒰 : X.OpenCover) :
    (⨆ i, (𝒰.map i).opensRange) = ⊤ :=
  Opens.ext <| by
    rw [Opens.coe_supᵢ]
    exact 𝒰.Union_range
#align algebraic_geometry.Scheme.open_cover.supr_opens_range AlgebraicGeometry.Scheme.OpenCover.supᵢ_opensRange

theorem Scheme.OpenCover.compactSpace {X : Scheme} (𝒰 : X.OpenCover) [Finite 𝒰.J]
    [H : ∀ i, CompactSpace (𝒰.obj i).carrier] : CompactSpace X.carrier :=
  by
  cases nonempty_fintype 𝒰.J
  rw [← isCompact_univ_iff, ← 𝒰.Union_range]
  apply isCompact_unionᵢ
  intro i
  rw [isCompact_iff_compactSpace]
  exact
    @homeomorph.compact_space _ _ (H i)
      (TopCat.homeoOfIso
        (asIso
          (IsOpenImmersion.isoOfRangeEq (𝒰.map i)
                  (X.of_restrict (Opens.openEmbedding ⟨_, (𝒰.is_open i).base_open.open_range⟩))
                  subtype.range_coe.symm).hom.1.base))
#align algebraic_geometry.Scheme.open_cover.compact_space AlgebraicGeometry.Scheme.OpenCover.compactSpace

/-- Given open covers `{ Uᵢ }` and `{ Uⱼ }`, we may form the open cover `{ Uᵢ ∩ Uⱼ }`. -/
def Scheme.OpenCover.inter {X : Scheme.{u}} (𝒰₁ : Scheme.OpenCover.{v₁} X)
    (𝒰₂ : Scheme.OpenCover.{v₂} X) : X.OpenCover
    where
  J := 𝒰₁.J × 𝒰₂.J
  obj ij := pullback (𝒰₁.map ij.1) (𝒰₂.map ij.2)
  map ij := pullback.fst ≫ 𝒰₁.map ij.1
  f x := ⟨𝒰₁.f x, 𝒰₂.f x⟩
  Covers x := by
    rw [IsOpenImmersion.range_pullback_to_base_of_left]
    exact ⟨𝒰₁.covers x, 𝒰₂.covers x⟩
#align algebraic_geometry.Scheme.open_cover.inter AlgebraicGeometry.Scheme.OpenCover.inter

/-- If `U` is a family of open sets that covers `X`, then `X.restrict U` forms an `X.open_cover`. -/
@[simps J obj map]
def Scheme.openCoverOfSuprEqTop {s : Type _} (X : Scheme) (U : s → Opens X.carrier)
    (hU : (⨆ i, U i) = ⊤) : X.OpenCover where
  J := s
  obj i := X.restrict (U i).openEmbedding
  map i := X.ofRestrict (U i).openEmbedding
  f x :=
    haveI : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : Opens X.carrier) by triv
    (opens.mem_supr.mp this).choose
  Covers x := by
    erw [Subtype.range_coe]
    have : x ∈ ⨆ i, U i := hU.symm ▸ show x ∈ (⊤ : Opens X.carrier) by triv
    exact (opens.mem_supr.mp this).choose_spec
#align algebraic_geometry.Scheme.open_cover_of_supr_eq_top AlgebraicGeometry.Scheme.openCoverOfSuprEqTop

section MorphismRestrict

/-- Given a morphism `f : X ⟶ Y` and an open set `U ⊆ Y`, we have `X ×[Y] U ≅ X |_{f ⁻¹ U}` -/
def pullbackRestrictIsoRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    pullback f (Y.ofRestrict U.openEmbedding) ≅
      X.restrict ((Opens.map f.1.base).obj U).openEmbedding :=
  by
  refine' IsOpenImmersion.isoOfRangeEq pullback.fst (X.of_restrict _) _
  rw [IsOpenImmersion.range_pullback_fst_of_right]
  dsimp [Opens.inclusion]
  rw [Subtype.range_coe, Subtype.range_coe]
  rfl
#align algebraic_geometry.pullback_restrict_iso_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict

@[simp, reassoc.1]
theorem pullbackRestrictIsoRestrict_inv_fst {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (pullbackRestrictIsoRestrict f U).inv ≫ pullback.fst = X.ofRestrict _ :=
  by
  delta pullback_restrict_iso_restrict
  simp
#align algebraic_geometry.pullback_restrict_iso_restrict_inv_fst AlgebraicGeometry.pullbackRestrictIsoRestrict_inv_fst

@[simp, reassoc.1]
theorem pullbackRestrictIsoRestrict_hom_restrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (pullbackRestrictIsoRestrict f U).hom ≫ X.ofRestrict _ = pullback.fst :=
  by
  delta pullback_restrict_iso_restrict
  simp
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_restrict

/-- The restriction of a morphism `X ⟶ Y` onto `X |_{f ⁻¹ U} ⟶ Y |_ U`. -/
def morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    X.restrict ((Opens.map f.1.base).obj U).openEmbedding ⟶ Y.restrict U.openEmbedding :=
  (pullbackRestrictIsoRestrict f U).inv ≫ pullback.snd
#align algebraic_geometry.morphism_restrict AlgebraicGeometry.morphismRestrict

-- mathport name: «expr ∣_ »
infixl:80 " ∣_ " => morphismRestrict

@[simp, reassoc.1]
theorem pullbackRestrictIsoRestrict_hom_morphismRestrict {X Y : Scheme} (f : X ⟶ Y)
    (U : Opens Y.carrier) : (pullbackRestrictIsoRestrict f U).hom ≫ f ∣_ U = pullback.snd :=
  Iso.hom_inv_id_assoc _ _
#align algebraic_geometry.pullback_restrict_iso_restrict_hom_morphism_restrict AlgebraicGeometry.pullbackRestrictIsoRestrict_hom_morphismRestrict

@[simp, reassoc.1]
theorem morphismRestrict_ι {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    (f ∣_ U) ≫ Y.ofRestrict U.openEmbedding = X.ofRestrict _ ≫ f :=
  by
  delta morphism_restrict
  rw [Category.assoc, pullback.condition.symm, pullbackRestrictIsoRestrict_inv_fst_assoc]
#align algebraic_geometry.morphism_restrict_ι AlgebraicGeometry.morphismRestrict_ι

theorem isPullbackMorphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    IsPullback (f ∣_ U) (X.ofRestrict _) (Y.ofRestrict _) f :=
  by
  delta morphism_restrict
  nth_rw 1 [← Category.id_comp f]
  refine'
    (IsPullback.ofHorizIsIso ⟨_⟩).pasteHoriz
      (IsPullback.ofHasPullback f (Y.of_restrict U.open_embedding)).flip
  rw [pullbackRestrictIsoRestrict_inv_fst, Category.comp_id]
#align algebraic_geometry.is_pullback_morphism_restrict AlgebraicGeometry.isPullbackMorphismRestrict

theorem morphismRestrict_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) (U : Opens Z.carrier) :
    (f ≫ g) ∣_ U = ((f ∣_ (Opens.map g.val.base).obj U) ≫ g ∣_ U : _) :=
  by
  delta morphism_restrict
  rw [← pullbackRightPullbackFstIso_inv_snd_snd]
  simp_rw [← Category.assoc]
  congr 1
  rw [← cancel_mono pullback.fst]
  simp_rw [Category.assoc]
  rw [pullbackRestrictIsoRestrict_inv_fst, pullbackRightPullbackFstIso_inv_snd_fst, ←
    pullback.condition, pullbackRestrictIsoRestrict_inv_fst_assoc,
    pullbackRestrictIsoRestrict_inv_fst_assoc]
  rfl
  infer_instance
#align algebraic_geometry.morphism_restrict_comp AlgebraicGeometry.morphismRestrict_comp

instance {X Y : Scheme} (f : X ⟶ Y) [IsIso f] (U : Opens Y.carrier) : IsIso (f ∣_ U) :=
  by
  delta morphism_restrict
  infer_instance

theorem morphismRestrict_base_coe {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (x) :
    @coe U Y.carrier _ ((f ∣_ U).1.base x) = f.1.base x.1 :=
  congr_arg (fun f => PresheafedSpace.Hom.base (LocallyRingedSpace.Hom.val f) x)
    (morphismRestrict_ι f U)
#align algebraic_geometry.morphism_restrict_base_coe AlgebraicGeometry.morphismRestrict_base_coe

theorem morphismRestrict_val_base {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    ⇑(f ∣_ U).1.base = U.1.restrictPreimage f.1.base :=
  funext fun x => Subtype.ext (morphismRestrict_base_coe f U x)
#align algebraic_geometry.morphism_restrict_val_base AlgebraicGeometry.morphismRestrict_val_base

theorem image_morphismRestrict_preimage {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier)
    (V : Opens U) :
    ((Opens.map f.val.base).obj U).openEmbedding.isOpenMap.functor.obj
        ((Opens.map (f ∣_ U).val.base).obj V) =
      (Opens.map f.val.base).obj (U.openEmbedding.isOpenMap.functor.obj V) :=
  by
  ext1
  ext x
  constructor
  · rintro ⟨⟨x, hx⟩, hx' : (f ∣_ U).1.base _ ∈ _, rfl⟩
    refine' ⟨⟨_, hx⟩, _, rfl⟩
    convert hx'
    ext1
    exact (morphismRestrict_base_coe f U ⟨x, hx⟩).symm
  · rintro ⟨⟨x, hx⟩, hx', rfl : x = _⟩
    refine' ⟨⟨_, hx⟩, (_ : (f ∣_ U).1.base ⟨x, hx⟩ ∈ V.1), rfl⟩
    convert hx'
    ext1
    exact morphismRestrict_base_coe f U ⟨x, hx⟩
#align algebraic_geometry.image_morphism_restrict_preimage AlgebraicGeometry.image_morphismRestrict_preimage

theorem morphismRestrict_c_app {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (V : Opens U) :
    (f ∣_ U).1.c.app (op V) =
      f.1.c.app (op (U.openEmbedding.isOpenMap.functor.obj V)) ≫
        X.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V)).op :=
  by
  have :=
    Scheme.congr_app (morphismRestrict_ι f U) (op (U.open_embedding.is_open_map.functor.obj V))
  rw [Scheme.comp_val_c_app, Scheme.comp_val_c_app_assoc] at this
  have e : (Opens.map U.inclusion).obj (U.open_embedding.is_open_map.functor.obj V) = V :=
    by
    ext1
    exact Set.preimage_image_eq _ Subtype.coe_injective
  have : _ ≫ X.presheaf.map _ = _ :=
    (((f ∣_ U).1.c.naturality (eqToHom e).op).symm.trans _).trans this
  swap
  · change Y.presheaf.map _ ≫ _ = Y.presheaf.map _ ≫ _
    congr
  rw [← IsIso.eq_comp_inv, ← Functor.map_inv, Category.assoc] at this
  rw [this]
  congr 1
  erw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
  congr 1
#align algebraic_geometry.morphism_restrict_c_app AlgebraicGeometry.morphismRestrict_c_app

theorem Γ_map_morphismRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) :
    Scheme.Γ.map (f ∣_ U).op =
      Y.presheaf.map (eqToHom <| U.openEmbedding_obj_top.symm).op ≫
        f.1.c.app (op U) ≫
          X.presheaf.map (eqToHom <| ((Opens.map f.val.base).obj U).openEmbedding_obj_top).op :=
  by
  rw [Scheme.Γ_map_op, morphismRestrict_c_app f U ⊤, f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr
#align algebraic_geometry.Γ_map_morphism_restrict AlgebraicGeometry.Γ_map_morphismRestrict

/-- Restricting a morphism onto the the image of an open immersion is isomorphic to the base change
along the immersion. -/
def morphismRestrictOpensRange {X Y U : Scheme} (f : X ⟶ Y) (g : U ⟶ Y) [hg : IsOpenImmersion g] :
    Arrow.mk (f ∣_ g.opensRange) ≅ Arrow.mk (pullback.snd : pullback f g ⟶ _) :=
  by
  let V : Opens Y.carrier := g.opens_range
  let e := IsOpenImmersion.isoOfRangeEq g (Y.of_restrict V.open_embedding) subtype.range_coe.symm
  let t : pullback f g ⟶ pullback f (Y.of_restrict V.open_embedding) :=
    pullback.map _ _ _ _ (𝟙 _) e.hom (𝟙 _) (by rw [Category.comp_id, Category.id_comp])
      (by rw [Category.comp_id, IsOpenImmersion.isoOfRangeEq_hom, IsOpenImmersion.lift_fac])
  symm
  refine' Arrow.isoMk (asIso t ≪≫ pullbackRestrictIsoRestrict f V) e _
  rw [Iso.trans_hom, asIso_hom, ← Iso.comp_inv_eq, ← cancel_mono g, Arrow.mk_hom, Arrow.mk_hom,
    IsOpenImmersion.isoOfRangeEq_inv, Category.assoc, Category.assoc, Category.assoc,
    IsOpenImmersion.lift_fac, ← pullback.condition, morphismRestrict_ι,
    pullbackRestrictIsoRestrict_hom_restrict_assoc, pullback.lift_fst_assoc, Category.comp_id]
#align algebraic_geometry.morphism_restrict_opens_range AlgebraicGeometry.morphismRestrictOpensRange

/-- The restrictions onto two equal open sets are isomorphic. This currently has bad defeqs when
unfolded, but it should not matter for now. Replace this definition if better defeqs are needed. -/
def morphismRestrictEq {X Y : Scheme} (f : X ⟶ Y) {U V : Opens Y.carrier} (e : U = V) :
    Arrow.mk (f ∣_ U) ≅ Arrow.mk (f ∣_ V) :=
  eqToIso (by subst e)
#align algebraic_geometry.morphism_restrict_eq AlgebraicGeometry.morphismRestrictEq

/-- Restricting a morphism twice is isomorpic to one restriction. -/
def morphismRestrictRestrict {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (V : Opens U) :
    Arrow.mk (f ∣_ U ∣_ V) ≅ Arrow.mk (f ∣_ U.openEmbedding.isOpenMap.functor.obj V) :=
  by
  have :
    (f ∣_ U ∣_ V) ≫ (Iso.refl _).hom =
      (asIso <|
            (pullbackRestrictIsoRestrict (f ∣_ U) V).inv ≫
              (pullbackSymmetry _ _).hom ≫
                pullback.map _ _ _ _ (𝟙 _)
                    ((pullbackRestrictIsoRestrict f U).inv ≫ (pullbackSymmetry _ _).hom) (𝟙 _)
                    ((Category.comp_id _).trans (Category.id_comp _).symm) (by simpa) ≫
                  (pullbackRightPullbackFstIso _ _ _).hom ≫ (pullbackSymmetry _ _).hom).hom ≫
        pullback.snd :=
    by
    simpa only [Category.comp_id, pullbackRightPullbackFstIso_hom_fst, Iso.refl_hom, Category.assoc,
      pullbackSymmetry_hom_comp_snd, asIso_hom, pullback.lift_fst, pullbackSymmetry_hom_comp_fst]
  refine'
    Arrow.isoMk' _ _ _ _ this.symm ≪≫
      (morphismRestrictOpensRange _ _).symm ≪≫ morphismRestrictEq _ _
  ext1
  dsimp
  rw [coe_comp, Set.range_comp]
  congr
  exact Subtype.range_coe
#align algebraic_geometry.morphism_restrict_restrict AlgebraicGeometry.morphismRestrictRestrict

/-- Restricting a morphism twice onto a basic open set is isomorphic to one restriction.  -/
def morphismRestrictRestrictBasicOpen {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier)
    (r : Y.presheaf.obj (op U)) :
    Arrow.mk
        (f ∣_ U ∣_
          (Y.restrict _).basicOpen (Y.presheaf.map (eqToHom U.openEmbedding_obj_top).op r)) ≅
      Arrow.mk (f ∣_ Y.basicOpen r) :=
  by
  refine' morphismRestrictRestrict _ _ _ ≪≫ morphismRestrictEq _ _
  have e := Scheme.preimage_basicOpen (Y.of_restrict U.open_embedding) r
  erw [Scheme.ofRestrict_val_c_app, Opens.adjunction_counit_app_self, eqToHom_op] at e
  rw [← (Y.restrict U.open_embedding).basicOpen_res_eq _ (eqToHom U.inclusion_map_eq_top).op, ←
    comp_apply]
  erw [← Y.presheaf.map_comp]
  rw [eqToHom_op, eqToHom_op, eqToHom_map, eqToHom_trans]
  erw [← e]
  ext1; dsimp [Opens.map, Opens.inclusion]
  rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left_iff_subset, Subtype.range_coe]
  exact Y.basic_open_le r
#align algebraic_geometry.morphism_restrict_restrict_basic_open AlgebraicGeometry.morphismRestrictRestrictBasicOpen

/-- The stalk map of a restriction of a morphism is isomorphic to the stalk map of the original map.
-/
def morphismRestrictStalkMap {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) (x) :
    Arrow.mk (PresheafedSpace.stalkMap (f ∣_ U).1 x) ≅
      Arrow.mk (PresheafedSpace.stalkMap f.1 x.1) :=
  by
  fapply Arrow.isoMk'
  · refine' Y.restrict_stalk_iso U.open_embedding ((f ∣_ U).1 x) ≪≫ TopCat.Presheaf.stalkCongr _ _
    apply Inseparable.of_eq
    exact morphismRestrict_base_coe f U x
  · exact X.restrict_stalk_iso _ _
  · apply TopCat.Presheaf.stalk_hom_ext
    intro V hxV
    simp only [TopCat.Presheaf.stalkCongr_hom, CategoryTheory.Category.assoc,
      CategoryTheory.Iso.trans_hom]
    erw [PresheafedSpace.restrictStalkIso_hom_eq_germ_assoc]
    erw [PresheafedSpace.stalkMap_germ_assoc _ _ ⟨_, _⟩]
    rw [TopCat.Presheaf.germ_stalk_specializes'_assoc]
    erw [PresheafedSpace.stalkMap_germ _ _ ⟨_, _⟩]
    erw [PresheafedSpace.restrictStalkIso_hom_eq_germ]
    rw [morphismRestrict_c_app, Category.assoc, TopCat.Presheaf.germ_res]
    rfl
#align algebraic_geometry.morphism_restrict_stalk_map AlgebraicGeometry.morphismRestrictStalkMap

instance {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier) [IsOpenImmersion f] :
    IsOpenImmersion (f ∣_ U) := by
  delta morphism_restrict
  infer_instance

end MorphismRestrict

end AlgebraicGeometry

