import Mathbin.CategoryTheory.Limits.Preserves.Basic

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace CategoryTheory

universe w' w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [category.{v₁} C]

section Creates

variable {D : Type u₂} [category.{v₂} D]

variable {J : Type w} [category.{w'} J] {K : J ⥤ C}

/-- Define the lift of a cone: For a cone `c` for `K ⋙ F`, give a cone for `K`
which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of limits:
every limit cone has a lift.

Note this definition is really only useful when `c` is a limit already.
-/
structure liftable_cone (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) where
  liftedCone : cone K
  validLift : F.map_cone lifted_cone ≅ c

/-- Define the lift of a cocone: For a cocone `c` for `K ⋙ F`, give a cocone for
`K` which is a lift of `c`, i.e. the image of it under `F` is (iso) to `c`.

We will then use this as part of the definition of creation of colimits:
every limit cocone has a lift.

Note this definition is really only useful when `c` is a colimit already.
-/
structure liftable_cocone (K : J ⥤ C) (F : C ⥤ D) (c : cocone (K ⋙ F)) where
  liftedCocone : cocone K
  validLift : F.map_cocone lifted_cocone ≅ c

/-- Definition 3.3.1 of [Riehl].
We say that `F` creates limits of `K` if, given any limit cone `c` for `K ⋙ F`
(i.e. below) we can lift it to a cone "above", and further that `F` reflects
limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class creates_limit (K : J ⥤ C) (F : C ⥤ D) extends reflects_limit K F where
  lifts : ∀ c, is_limit c → liftable_cone K F c

/-- `F` creates limits of shape `J` if `F` creates the limit of any diagram
`K : J ⥤ C`.
-/
class creates_limits_of_shape (J : Type w) [category.{w'} J] (F : C ⥤ D) where
  CreatesLimit : ∀ {K : J ⥤ C}, creates_limit K F := by
    run_tac
      tactic.apply_instance

/-- `F` creates limits if it creates limits of shape `J` for any `J`. -/
@[nolint check_univs]
class creates_limits_of_size (F : C ⥤ D) where
  CreatesLimitsOfShape : ∀ {J : Type w} [category.{w'} J], creates_limits_of_shape J F := by
    run_tac
      tactic.apply_instance

/-- `F` creates small limits if it creates limits of shape `J` for any small `J`. -/
abbrev creates_limits (F : C ⥤ D) :=
  creates_limits_of_size.{v₂, v₂} F

/-- Dual of definition 3.3.1 of [Riehl].
We say that `F` creates colimits of `K` if, given any limit cocone `c` for
`K ⋙ F` (i.e. below) we can lift it to a cocone "above", and further that `F`
reflects limits for `K`.

If `F` reflects isomorphisms, it suffices to show only that the lifted cocone is
a limit - see `creates_limit_of_reflects_iso`.
-/
class creates_colimit (K : J ⥤ C) (F : C ⥤ D) extends reflects_colimit K F where
  lifts : ∀ c, is_colimit c → liftable_cocone K F c

/-- `F` creates colimits of shape `J` if `F` creates the colimit of any diagram
`K : J ⥤ C`.
-/
class creates_colimits_of_shape (J : Type w) [category.{w'} J] (F : C ⥤ D) where
  CreatesColimit : ∀ {K : J ⥤ C}, creates_colimit K F := by
    run_tac
      tactic.apply_instance

/-- `F` creates colimits if it creates colimits of shape `J` for any small `J`. -/
@[nolint check_univs]
class creates_colimits_of_size (F : C ⥤ D) where
  CreatesColimitsOfShape : ∀ {J : Type w} [category.{w'} J], creates_colimits_of_shape J F := by
    run_tac
      tactic.apply_instance

/-- `F` creates small colimits if it creates colimits of shape `J` for any small `J`. -/
abbrev creates_colimits (F : C ⥤ D) :=
  creates_colimits_of_size.{v₂, v₂} F

attribute [instance]
  creates_limits_of_shape.creates_limit creates_limits_of_size.creates_limits_of_shape creates_colimits_of_shape.creates_colimit creates_colimits_of_size.creates_colimits_of_shape

/-- `lift_limit t` is the cone for `K` given by lifting the limit `t` for `K ⋙ F`. -/
def lift_limit {K : J ⥤ C} {F : C ⥤ D} [creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) : cone K :=
  (creates_limit.lifts c t).liftedCone

/-- The lifted cone has an image isomorphic to the original cone. -/
def lifted_limit_maps_to_original {K : J ⥤ C} {F : C ⥤ D} [creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) :
    F.map_cone (lift_limit t) ≅ c :=
  (creates_limit.lifts c t).validLift

/-- The lifted cone is a limit. -/
def lifted_limit_is_limit {K : J ⥤ C} {F : C ⥤ D} [creates_limit K F] {c : cone (K ⋙ F)} (t : is_limit c) :
    is_limit (lift_limit t) :=
  reflects_limit.reflects (is_limit.of_iso_limit t (lifted_limit_maps_to_original t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem has_limit_of_created (K : J ⥤ C) (F : C ⥤ D) [has_limit (K ⋙ F)] [creates_limit K F] : has_limit K :=
  has_limit.mk { Cone := lift_limit (limit.is_limit (K ⋙ F)), IsLimit := lifted_limit_is_limit _ }

/-- If `F` creates limits of shape `J`, and `D` has limits of shape `J`, then
`C` has limits of shape `J`.
-/
theorem has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape (F : C ⥤ D) [has_limits_of_shape J D]
    [creates_limits_of_shape J F] : has_limits_of_shape J C :=
  ⟨fun G => has_limit_of_created G F⟩

/-- If `F` creates limits, and `D` has all limits, then `C` has all limits. -/
theorem has_limits_of_has_limits_creates_limits (F : C ⥤ D) [has_limits_of_size.{w, w'} D]
    [creates_limits_of_size.{w, w'} F] : has_limits_of_size.{w, w'} C :=
  ⟨fun J I => has_limits_of_shape_of_has_limits_of_shape_creates_limits_of_shape F⟩

/-- `lift_colimit t` is the cocone for `K` given by lifting the colimit `t` for `K ⋙ F`. -/
def lift_colimit {K : J ⥤ C} {F : C ⥤ D} [creates_colimit K F] {c : cocone (K ⋙ F)} (t : is_colimit c) : cocone K :=
  (creates_colimit.lifts c t).liftedCocone

/-- The lifted cocone has an image isomorphic to the original cocone. -/
def lifted_colimit_maps_to_original {K : J ⥤ C} {F : C ⥤ D} [creates_colimit K F] {c : cocone (K ⋙ F)}
    (t : is_colimit c) : F.map_cocone (lift_colimit t) ≅ c :=
  (creates_colimit.lifts c t).validLift

/-- The lifted cocone is a colimit. -/
def lifted_colimit_is_colimit {K : J ⥤ C} {F : C ⥤ D} [creates_colimit K F] {c : cocone (K ⋙ F)} (t : is_colimit c) :
    is_colimit (lift_colimit t) :=
  reflects_colimit.reflects (is_colimit.of_iso_colimit t (lifted_colimit_maps_to_original t).symm)

/-- If `F` creates the limit of `K` and `K ⋙ F` has a limit, then `K` has a limit. -/
theorem has_colimit_of_created (K : J ⥤ C) (F : C ⥤ D) [has_colimit (K ⋙ F)] [creates_colimit K F] : has_colimit K :=
  has_colimit.mk { Cocone := lift_colimit (colimit.is_colimit (K ⋙ F)), IsColimit := lifted_colimit_is_colimit _ }

/-- If `F` creates colimits of shape `J`, and `D` has colimits of shape `J`, then
`C` has colimits of shape `J`.
-/
theorem has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape (F : C ⥤ D) [has_colimits_of_shape J D]
    [creates_colimits_of_shape J F] : has_colimits_of_shape J C :=
  ⟨fun G => has_colimit_of_created G F⟩

/-- If `F` creates colimits, and `D` has all colimits, then `C` has all colimits. -/
theorem has_colimits_of_has_colimits_creates_colimits (F : C ⥤ D) [has_colimits_of_size.{w, w'} D]
    [creates_colimits_of_size.{w, w'} F] : has_colimits_of_size.{w, w'} C :=
  ⟨fun J I => has_colimits_of_shape_of_has_colimits_of_shape_creates_colimits_of_shape F⟩

instance (priority := 10) reflects_limits_of_shape_of_creates_limits_of_shape (F : C ⥤ D)
    [creates_limits_of_shape J F] : reflects_limits_of_shape J F :=
  {  }

instance (priority := 10) reflects_limits_of_creates_limits (F : C ⥤ D) [creates_limits_of_size.{w, w'} F] :
    reflects_limits_of_size.{w, w'} F :=
  {  }

instance (priority := 10) reflects_colimits_of_shape_of_creates_colimits_of_shape (F : C ⥤ D)
    [creates_colimits_of_shape J F] : reflects_colimits_of_shape J F :=
  {  }

instance (priority := 10) reflects_colimits_of_creates_colimits (F : C ⥤ D) [creates_colimits_of_size.{w, w'} F] :
    reflects_colimits_of_size.{w, w'} F :=
  {  }

/-- A helper to show a functor creates limits. In particular, if we can show
that for any limit cone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates limits.
Usually, `F` creating limits says that _any_ lift of `c` is a limit, but
here we only need to show that our particular lift of `c` is a limit.
-/
structure lifts_to_limit (K : J ⥤ C) (F : C ⥤ D) (c : cone (K ⋙ F)) (t : is_limit c) extends liftable_cone K F c where
  makesLimit : is_limit lifted_cone

/-- A helper to show a functor creates colimits. In particular, if we can show
that for any limit cocone `c` for `K ⋙ F`, there is a lift of it which is
a limit and `F` reflects isomorphisms, then `F` creates colimits.
Usually, `F` creating colimits says that _any_ lift of `c` is a colimit, but
here we only need to show that our particular lift of `c` is a colimit.
-/
structure lifts_to_colimit (K : J ⥤ C) (F : C ⥤ D) (c : cocone (K ⋙ F)) (t : is_colimit c) extends
  liftable_cocone K F c where
  makesColimit : is_colimit lifted_cocone

/-- If `F` reflects isomorphisms and we can lift any limit cone to a limit cone,
then `F` creates limits.
In particular here we don't need to assume that F reflects limits.
-/
def creates_limit_of_reflects_iso {K : J ⥤ C} {F : C ⥤ D} [reflects_isomorphisms F]
    (h : ∀ c t, lifts_to_limit K F c t) : creates_limit K F where
  lifts := fun c t => (h c t).toLiftableCone
  toReflectsLimit :=
    { reflects := fun d : cone K hd : is_limit (F.map_cone d) => by
        let d' : cone K := (h (F.map_cone d) hd).toLiftableCone.liftedCone
        let i : F.map_cone d' ≅ F.map_cone d := (h (F.map_cone d) hd).toLiftableCone.validLift
        let hd' : is_limit d' := (h (F.map_cone d) hd).makesLimit
        let f : d ⟶ d' := hd'.lift_cone_morphism d
        have : (cones.functoriality K F).map f = i.inv := (hd.of_iso_limit i.symm).uniq_cone_morphism
        have : is_iso ((cones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        have : is_iso f := is_iso_of_reflects_iso f (cones.functoriality K F)
        exact is_limit.of_iso_limit hd' (as_iso f).symm }

/-- When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to exhibit a lift of the chosen limit cone for `K ⋙ F`.
-/
def creates_limit_of_fully_faithful_of_lift {K : J ⥤ C} {F : C ⥤ D} [full F] [faithful F] [has_limit (K ⋙ F)]
    (c : cone K) (i : F.map_cone c ≅ limit.cone (K ⋙ F)) : creates_limit K F :=
  creates_limit_of_reflects_iso fun c' t =>
    { liftedCone := c, validLift := i.trans (is_limit.unique_up_to_iso (limit.is_limit _) t),
      makesLimit :=
        is_limit.of_faithful F (is_limit.of_iso_limit (limit.is_limit _) i.symm) (fun s => F.preimage _) fun s =>
          F.image_preimage _ }

/-- When `F` is fully faithful, and `has_limit (K ⋙ F)`, to show that `F` creates the limit for `K`
it suffices to show that the chosen limit point is in the essential image of `F`.
-/
def creates_limit_of_fully_faithful_of_iso {K : J ⥤ C} {F : C ⥤ D} [full F] [faithful F] [has_limit (K ⋙ F)] (X : C)
    (i : F.obj X ≅ limit (K ⋙ F)) : creates_limit K F :=
  creates_limit_of_fully_faithful_of_lift
    ({ x,
      π :=
        { app := fun j => F.preimage (i.hom ≫ limit.π (K ⋙ F) j),
          naturality' := fun Y Z f =>
            F.map_injective
              (by
                dsimp
                simp
                erw [limit.w (K ⋙ F)]) } } :
      cone K)
    (by
      fapply cones.ext
      exact i
      tidy)

/-- `F` preserves the limit of `K` if it creates the limit and `K ⋙ F` has the limit. -/
instance (priority := 100) preserves_limit_of_creates_limit_and_has_limit (K : J ⥤ C) (F : C ⥤ D) [creates_limit K F]
    [has_limit (K ⋙ F)] : preserves_limit K F where
  preserves := fun c t =>
    is_limit.of_iso_limit (limit.is_limit _)
      ((lifted_limit_maps_to_original (limit.is_limit _)).symm ≪≫
        (cones.functoriality K F).mapIso ((lifted_limit_is_limit (limit.is_limit _)).uniqueUpToIso t))

/-- `F` preserves the limit of shape `J` if it creates these limits and `D` has them. -/
instance (priority := 100) preserves_limit_of_shape_of_creates_limits_of_shape_and_has_limits_of_shape (F : C ⥤ D)
    [creates_limits_of_shape J F] [has_limits_of_shape J D] : preserves_limits_of_shape J F :=
  {  }

/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preserves_limits_of_creates_limits_and_has_limits (F : C ⥤ D)
    [creates_limits_of_size.{w, w'} F] [has_limits_of_size.{w, w'} D] : preserves_limits_of_size.{w, w'} F :=
  {  }

/-- If `F` reflects isomorphisms and we can lift any colimit cocone to a colimit cocone,
then `F` creates colimits.
In particular here we don't need to assume that F reflects colimits.
-/
def creates_colimit_of_reflects_iso {K : J ⥤ C} {F : C ⥤ D} [reflects_isomorphisms F]
    (h : ∀ c t, lifts_to_colimit K F c t) : creates_colimit K F where
  lifts := fun c t => (h c t).toLiftableCocone
  toReflectsColimit :=
    { reflects := fun d : cocone K hd : is_colimit (F.map_cocone d) => by
        let d' : cocone K := (h (F.map_cocone d) hd).toLiftableCocone.liftedCocone
        let i : F.map_cocone d' ≅ F.map_cocone d := (h (F.map_cocone d) hd).toLiftableCocone.validLift
        let hd' : is_colimit d' := (h (F.map_cocone d) hd).makesColimit
        let f : d' ⟶ d := hd'.desc_cocone_morphism d
        have : (cocones.functoriality K F).map f = i.hom := (hd.of_iso_colimit i.symm).uniq_cocone_morphism
        have : is_iso ((cocones.functoriality K F).map f) := by
          rw [this]
          infer_instance
        have := is_iso_of_reflects_iso f (cocones.functoriality K F)
        exact is_colimit.of_iso_colimit hd' (as_iso f) }

/-- When `F` is fully faithful, and `has_colimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to exhibit a lift of the chosen colimit cocone for `K ⋙ F`.
-/
def creates_colimit_of_fully_faithful_of_lift {K : J ⥤ C} {F : C ⥤ D} [full F] [faithful F] [has_colimit (K ⋙ F)]
    (c : cocone K) (i : F.map_cocone c ≅ colimit.cocone (K ⋙ F)) : creates_colimit K F :=
  creates_colimit_of_reflects_iso fun c' t =>
    { liftedCocone := c, validLift := i.trans (is_colimit.unique_up_to_iso (colimit.is_colimit _) t),
      makesColimit :=
        is_colimit.of_faithful F (is_colimit.of_iso_colimit (colimit.is_colimit _) i.symm) (fun s => F.preimage _)
          fun s => F.image_preimage _ }

/-- When `F` is fully faithful, and `has_colimit (K ⋙ F)`, to show that `F` creates the colimit for `K`
it suffices to show that the chosen colimit point is in the essential image of `F`.
-/
def creates_colimit_of_fully_faithful_of_iso {K : J ⥤ C} {F : C ⥤ D} [full F] [faithful F] [has_colimit (K ⋙ F)] (X : C)
    (i : F.obj X ≅ colimit (K ⋙ F)) : creates_colimit K F :=
  creates_colimit_of_fully_faithful_of_lift
    ({ x,
      ι :=
        { app := fun j => F.preimage (colimit.ι (K ⋙ F) j ≫ i.inv : _),
          naturality' := fun Y Z f =>
            F.map_injective
              (by
                erw [category.comp_id]
                simp only [functor.map_comp, functor.image_preimage]
                erw [colimit.w_assoc (K ⋙ F)]) } } :
      cocone K)
    (by
      fapply cocones.ext
      exact i
      tidy)

/-- `F` preserves the colimit of `K` if it creates the colimit and `K ⋙ F` has the colimit. -/
instance (priority := 100) preserves_colimit_of_creates_colimit_and_has_colimit (K : J ⥤ C) (F : C ⥤ D)
    [creates_colimit K F] [has_colimit (K ⋙ F)] : preserves_colimit K F where
  preserves := fun c t =>
    is_colimit.of_iso_colimit (colimit.is_colimit _)
      ((lifted_colimit_maps_to_original (colimit.is_colimit _)).symm ≪≫
        (cocones.functoriality K F).mapIso ((lifted_colimit_is_colimit (colimit.is_colimit _)).uniqueUpToIso t))

/-- `F` preserves the colimit of shape `J` if it creates these colimits and `D` has them. -/
instance (priority := 100) preserves_colimit_of_shape_of_creates_colimits_of_shape_and_has_colimits_of_shape (F : C ⥤ D)
    [creates_colimits_of_shape J F] [has_colimits_of_shape J D] : preserves_colimits_of_shape J F :=
  {  }

/-- `F` preserves limits if it creates limits and `D` has limits. -/
instance (priority := 100) preserves_colimits_of_creates_colimits_and_has_colimits (F : C ⥤ D)
    [creates_colimits_of_size.{w, w'} F] [has_colimits_of_size.{w, w'} D] : preserves_colimits_of_size.{w, w'} F :=
  {  }

/-- Transfer creation of limits along a natural isomorphism in the diagram. -/
def creates_limit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [creates_limit K₁ F] : creates_limit K₂ F :=
  { reflects_limit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (is_limit.postcompose_inv_equiv (iso_whisker_right h F : _) c).symm t
      { liftedCone := (cones.postcompose h.hom).obj (lift_limit t'),
        validLift :=
          F.map_cone_postcompose ≪≫
            (cones.postcompose (iso_whisker_right h F).Hom).mapIso (lifted_limit_maps_to_original t') ≪≫
              cones.ext (iso.refl _) fun j => by
                dsimp
                rw [category.assoc, ← F.map_comp]
                simp } }

/-- If `F` creates the limit of `K` and `F ≅ G`, then `G` creates the limit of `K`. -/
def creates_limit_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [creates_limit K F] : creates_limit K G where
  lifts := fun c t =>
    { liftedCone := lift_limit ((is_limit.postcompose_inv_equiv (iso_whisker_left K h : _) c).symm t),
      validLift := by
        refine' (is_limit.map_cone_equiv h _).uniqueUpToIso t
        apply is_limit.of_iso_limit _ (lifted_limit_maps_to_original _).symm
        apply (is_limit.postcompose_inv_equiv _ _).symm t }
  toReflectsLimit := reflects_limit_of_nat_iso _ h

/-- If `F` creates limits of shape `J` and `F ≅ G`, then `G` creates limits of shape `J`. -/
def creates_limits_of_shape_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [creates_limits_of_shape J F] :
    creates_limits_of_shape J G where
  CreatesLimit := fun K => creates_limit_of_nat_iso h

/-- If `F` creates limits and `F ≅ G`, then `G` creates limits. -/
def creates_limits_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [creates_limits_of_size.{w, w'} F] :
    creates_limits_of_size.{w, w'} G where
  CreatesLimitsOfShape := fun J 𝒥₁ => creates_limits_of_shape_of_nat_iso h

/-- Transfer creation of colimits along a natural isomorphism in the diagram. -/
def creates_colimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [creates_colimit K₁ F] :
    creates_colimit K₂ F :=
  { reflects_colimit_of_iso_diagram F h with
    lifts := fun c t =>
      let t' := (is_colimit.precompose_hom_equiv (iso_whisker_right h F : _) c).symm t
      { liftedCocone := (cocones.precompose h.inv).obj (lift_colimit t'),
        validLift :=
          F.map_cocone_precompose ≪≫
            (cocones.precompose (iso_whisker_right h F).inv).mapIso (lifted_colimit_maps_to_original t') ≪≫
              cocones.ext (iso.refl _) fun j => by
                dsimp
                rw [← F.map_comp_assoc]
                simp } }

/-- If `F` creates the colimit of `K` and `F ≅ G`, then `G` creates the colimit of `K`. -/
def creates_colimit_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [creates_colimit K F] : creates_colimit K G where
  lifts := fun c t =>
    { liftedCocone := lift_colimit ((is_colimit.precompose_hom_equiv (iso_whisker_left K h : _) c).symm t),
      validLift := by
        refine' (is_colimit.map_cocone_equiv h _).uniqueUpToIso t
        apply is_colimit.of_iso_colimit _ (lifted_colimit_maps_to_original _).symm
        apply (is_colimit.precompose_hom_equiv _ _).symm t }
  toReflectsColimit := reflects_colimit_of_nat_iso _ h

/-- If `F` creates colimits of shape `J` and `F ≅ G`, then `G` creates colimits of shape `J`. -/
def creates_colimits_of_shape_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [creates_colimits_of_shape J F] :
    creates_colimits_of_shape J G where
  CreatesColimit := fun K => creates_colimit_of_nat_iso h

/-- If `F` creates colimits and `F ≅ G`, then `G` creates colimits. -/
def creates_colimits_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [creates_colimits_of_size.{w, w'} F] :
    creates_colimits_of_size.{w, w'} G where
  CreatesColimitsOfShape := fun J 𝒥₁ => creates_colimits_of_shape_of_nat_iso h

/-- If F creates the limit of K, any cone lifts to a limit. -/
def lifts_to_limit_of_creates (K : J ⥤ C) (F : C ⥤ D) [creates_limit K F] (c : cone (K ⋙ F)) (t : is_limit c) :
    lifts_to_limit K F c t where
  liftedCone := lift_limit t
  validLift := lifted_limit_maps_to_original t
  makesLimit := lifted_limit_is_limit t

/-- If F creates the colimit of K, any cocone lifts to a colimit. -/
def lifts_to_colimit_of_creates (K : J ⥤ C) (F : C ⥤ D) [creates_colimit K F] (c : cocone (K ⋙ F)) (t : is_colimit c) :
    lifts_to_colimit K F c t where
  liftedCocone := lift_colimit t
  validLift := lifted_colimit_maps_to_original t
  makesColimit := lifted_colimit_is_colimit t

/-- Any cone lifts through the identity functor. -/
def id_lifts_cone (c : cone (K ⋙ 𝟭 C)) : liftable_cone K (𝟭 C) c where
  liftedCone := { x := c.X, π := c.π ≫ K.right_unitor.hom }
  validLift :=
    cones.ext (iso.refl _)
      (by
        tidy)

/-- The identity functor creates all limits. -/
instance id_creates_limits : creates_limits_of_size.{w, w'} (𝟭 C) where
  CreatesLimitsOfShape := fun J 𝒥 => { CreatesLimit := fun F => { lifts := fun c t => id_lifts_cone c } }

/-- Any cocone lifts through the identity functor. -/
def id_lifts_cocone (c : cocone (K ⋙ 𝟭 C)) : liftable_cocone K (𝟭 C) c where
  liftedCocone := { x := c.X, ι := K.right_unitor.inv ≫ c.ι }
  validLift :=
    cocones.ext (iso.refl _)
      (by
        tidy)

/-- The identity functor creates all colimits. -/
instance id_creates_colimits : creates_colimits_of_size.{w, w'} (𝟭 C) where
  CreatesColimitsOfShape := fun J 𝒥 => { CreatesColimit := fun F => { lifts := fun c t => id_lifts_cocone c } }

/-- Satisfy the inhabited linter -/
instance inhabited_liftable_cone (c : cone (K ⋙ 𝟭 C)) : Inhabited (liftable_cone K (𝟭 C) c) :=
  ⟨id_lifts_cone c⟩

instance inhabited_liftable_cocone (c : cocone (K ⋙ 𝟭 C)) : Inhabited (liftable_cocone K (𝟭 C) c) :=
  ⟨id_lifts_cocone c⟩

/-- Satisfy the inhabited linter -/
instance inhabited_lifts_to_limit (K : J ⥤ C) (F : C ⥤ D) [creates_limit K F] (c : cone (K ⋙ F)) (t : is_limit c) :
    Inhabited (lifts_to_limit _ _ _ t) :=
  ⟨lifts_to_limit_of_creates K F c t⟩

instance inhabited_lifts_to_colimit (K : J ⥤ C) (F : C ⥤ D) [creates_colimit K F] (c : cocone (K ⋙ F))
    (t : is_colimit c) : Inhabited (lifts_to_colimit _ _ _ t) :=
  ⟨lifts_to_colimit_of_creates K F c t⟩

section Comp

variable {E : Type u₃} [ℰ : category.{v₃} E]

variable (F : C ⥤ D) (G : D ⥤ E)

instance comp_creates_limit [creates_limit K F] [creates_limit (K ⋙ F) G] : creates_limit K (F ⋙ G) where
  lifts := fun c t =>
    { liftedCone := lift_limit (lifted_limit_is_limit t),
      validLift :=
        (cones.functoriality (K ⋙ F) G).mapIso (lifted_limit_maps_to_original (lifted_limit_is_limit t)) ≪≫
          lifted_limit_maps_to_original t }

instance comp_creates_limits_of_shape [creates_limits_of_shape J F] [creates_limits_of_shape J G] :
    creates_limits_of_shape J (F ⋙ G) where
  CreatesLimit := inferInstance

instance comp_creates_limits [creates_limits_of_size.{w, w'} F] [creates_limits_of_size.{w, w'} G] :
    creates_limits_of_size.{w, w'} (F ⋙ G) where
  CreatesLimitsOfShape := inferInstance

instance comp_creates_colimit [creates_colimit K F] [creates_colimit (K ⋙ F) G] : creates_colimit K (F ⋙ G) where
  lifts := fun c t =>
    { liftedCocone := lift_colimit (lifted_colimit_is_colimit t),
      validLift :=
        (cocones.functoriality (K ⋙ F) G).mapIso (lifted_colimit_maps_to_original (lifted_colimit_is_colimit t)) ≪≫
          lifted_colimit_maps_to_original t }

instance comp_creates_colimits_of_shape [creates_colimits_of_shape J F] [creates_colimits_of_shape J G] :
    creates_colimits_of_shape J (F ⋙ G) where
  CreatesColimit := inferInstance

instance comp_creates_colimits [creates_colimits_of_size.{w, w'} F] [creates_colimits_of_size.{w, w'} G] :
    creates_colimits_of_size.{w, w'} (F ⋙ G) where
  CreatesColimitsOfShape := inferInstance

end Comp

end Creates

end CategoryTheory

