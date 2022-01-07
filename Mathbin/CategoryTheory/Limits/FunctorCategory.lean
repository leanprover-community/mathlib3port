import Mathbin.CategoryTheory.Limits.Preserves.Limits

/-!
# (Co)limits in functor categories.

We show that if `D` has limits, then the functor category `C ⥤ D` also has limits
(`category_theory.limits.functor_category_has_limits`),
and the evaluation functors preserve limits
(`category_theory.limits.evaluation_preserves_limits`)
(and similarly for colimits).

We also show that `F : D ⥤ K ⥤ C` preserves (co)limits if it does so for each `k : K`
(`category_theory.limits.preserves_limits_of_evaluation` and
`category_theory.limits.preserves_colimits_of_evaluation`).
-/


open CategoryTheory CategoryTheory.Category

universe v₁ v₂ u₁ u₂ v v' u u'

namespace CategoryTheory.Limits

variable {C : Type u} [category.{v} C] {D : Type u'} [category.{v'} D]

variable {J : Type u₁} [category.{v₁} J] {K : Type u₂} [category.{v₂} K]

@[simp, reassoc]
theorem limit.lift_π_app (H : J ⥤ K ⥤ C) [has_limit H] (c : cone H) (j : J) (k : K) :
    (limit.lift H c).app k ≫ (limit.π H j).app k = (c.π.app j).app k :=
  congr_app (limit.lift_π c j) k

@[simp, reassoc]
theorem colimit.ι_desc_app (H : J ⥤ K ⥤ C) [has_colimit H] (c : cocone H) (j : J) (k : K) :
    (colimit.ι H j).app k ≫ (colimit.desc H c).app k = (c.ι.app j).app k :=
  congr_app (colimit.ι_desc c j) k

/-- The evaluation functors jointly reflect limits: that is, to show a cone is a limit of `F`
it suffices to show that each evaluation cone is a limit. In other words, to prove a cone is
limiting you can show it's pointwise limiting.
-/
def evaluation_jointly_reflects_limits {F : J ⥤ K ⥤ C} (c : cone F)
    (t : ∀ k : K, is_limit (((evaluation K C).obj k).mapCone c)) : is_limit c where
  lift := fun s =>
    { app := fun k => (t k).lift ⟨s.X.obj k, whisker_right s.π ((evaluation K C).obj k)⟩,
      naturality' := fun X Y f =>
        (t Y).hom_ext $ fun j => by
          rw [assoc, (t Y).fac _ j]
          simpa using ((t X).fac_assoc ⟨s.X.obj X, whisker_right s.π ((evaluation K C).obj X)⟩ j _).symm }
  fac' := fun s j => nat_trans.ext _ _ $ funext $ fun k => (t k).fac _ j
  uniq' := fun s m w =>
    nat_trans.ext _ _ $
      funext $ fun x =>
        (t x).hom_ext $ fun j =>
          (congr_app (w j) x).trans ((t x).fac ⟨s.X.obj _, whisker_right s.π ((evaluation K C).obj _)⟩ j).symm

/-- Given a functor `F` and a collection of limit cones for each diagram `X ↦ F X k`, we can stitch
them together to give a cone for the diagram `F`.
`combined_is_limit` shows that the new cone is limiting, and `eval_combined` shows it is
(essentially) made up of the original cones.
-/
@[simps]
def combine_cones (F : J ⥤ K ⥤ C) (c : ∀ k : K, limit_cone (F.flip.obj k)) : cone F where
  x :=
    { obj := fun k => (c k).Cone.x, map := fun k₁ k₂ f => (c k₂).IsLimit.lift ⟨_, (c k₁).Cone.π ≫ F.flip.map f⟩,
      map_id' := fun k =>
        (c k).IsLimit.hom_ext fun j => by
          dsimp
          simp ,
      map_comp' := fun k₁ k₂ k₃ f₁ f₂ =>
        (c k₃).IsLimit.hom_ext fun j => by
          simp }
  π :=
    { app := fun j => { app := fun k => (c k).Cone.π.app j },
      naturality' := fun j₁ j₂ g => nat_trans.ext _ _ $ funext $ fun k => (c k).Cone.π.naturality g }

/-- The stitched together cones each project down to the original given cones (up to iso). -/
def evaluate_combined_cones (F : J ⥤ K ⥤ C) (c : ∀ k : K, limit_cone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCone (combine_cones F c) ≅ (c k).Cone :=
  cones.ext (iso.refl _)
    (by
      tidy)

/-- Stitching together limiting cones gives a limiting cone. -/
def combined_is_limit (F : J ⥤ K ⥤ C) (c : ∀ k : K, limit_cone (F.flip.obj k)) : is_limit (combine_cones F c) :=
  evaluation_jointly_reflects_limits _ fun k => (c k).IsLimit.ofIsoLimit (evaluate_combined_cones F c k).symm

/-- The evaluation functors jointly reflect colimits: that is, to show a cocone is a colimit of `F`
it suffices to show that each evaluation cocone is a colimit. In other words, to prove a cocone is
colimiting you can show it's pointwise colimiting.
-/
def evaluation_jointly_reflects_colimits {F : J ⥤ K ⥤ C} (c : cocone F)
    (t : ∀ k : K, is_colimit (((evaluation K C).obj k).mapCocone c)) : is_colimit c where
  desc := fun s =>
    { app := fun k => (t k).desc ⟨s.X.obj k, whisker_right s.ι ((evaluation K C).obj k)⟩,
      naturality' := fun X Y f =>
        (t X).hom_ext $ fun j => by
          rw [(t X).fac_assoc _ j]
          erw [← (c.ι.app j).naturality_assoc f]
          erw [(t Y).fac ⟨s.X.obj _, whisker_right s.ι _⟩ j]
          dsimp
          simp }
  fac' := fun s j => nat_trans.ext _ _ $ funext $ fun k => (t k).fac _ j
  uniq' := fun s m w =>
    nat_trans.ext _ _ $
      funext $ fun x =>
        (t x).hom_ext $ fun j =>
          (congr_app (w j) x).trans ((t x).fac ⟨s.X.obj _, whisker_right s.ι ((evaluation K C).obj _)⟩ j).symm

/-- Given a functor `F` and a collection of colimit cocones for each diagram `X ↦ F X k`, we can stitch
them together to give a cocone for the diagram `F`.
`combined_is_colimit` shows that the new cocone is colimiting, and `eval_combined` shows it is
(essentially) made up of the original cocones.
-/
@[simps]
def combine_cocones (F : J ⥤ K ⥤ C) (c : ∀ k : K, colimit_cocone (F.flip.obj k)) : cocone F where
  x :=
    { obj := fun k => (c k).Cocone.x, map := fun k₁ k₂ f => (c k₁).IsColimit.desc ⟨_, F.flip.map f ≫ (c k₂).Cocone.ι⟩,
      map_id' := fun k =>
        (c k).IsColimit.hom_ext fun j => by
          dsimp
          simp ,
      map_comp' := fun k₁ k₂ k₃ f₁ f₂ =>
        (c k₁).IsColimit.hom_ext fun j => by
          simp }
  ι :=
    { app := fun j => { app := fun k => (c k).Cocone.ι.app j },
      naturality' := fun j₁ j₂ g => nat_trans.ext _ _ $ funext $ fun k => (c k).Cocone.ι.naturality g }

/-- The stitched together cocones each project down to the original given cocones (up to iso). -/
def evaluate_combined_cocones (F : J ⥤ K ⥤ C) (c : ∀ k : K, colimit_cocone (F.flip.obj k)) (k : K) :
    ((evaluation K C).obj k).mapCocone (combine_cocones F c) ≅ (c k).Cocone :=
  cocones.ext (iso.refl _)
    (by
      tidy)

/-- Stitching together colimiting cocones gives a colimiting cocone. -/
def combined_is_colimit (F : J ⥤ K ⥤ C) (c : ∀ k : K, colimit_cocone (F.flip.obj k)) :
    is_colimit (combine_cocones F c) :=
  evaluation_jointly_reflects_colimits _ fun k => (c k).IsColimit.ofIsoColimit (evaluate_combined_cocones F c k).symm

noncomputable section

instance functor_category_has_limits_of_shape [has_limits_of_shape J C] : has_limits_of_shape J (K ⥤ C) where
  HasLimit := fun F =>
    has_limit.mk { Cone := combine_cones F fun k => get_limit_cone _, IsLimit := combined_is_limit _ _ }

instance functor_category_has_colimits_of_shape [has_colimits_of_shape J C] : has_colimits_of_shape J (K ⥤ C) where
  HasColimit := fun F =>
    has_colimit.mk { Cocone := combine_cocones _ fun k => get_colimit_cocone _, IsColimit := combined_is_colimit _ _ }

instance functor_category_has_limits_of_size [has_limits_of_size.{v₁, u₁} C] : has_limits_of_size.{v₁, u₁} (K ⥤ C) :=
  ⟨inferInstance⟩

instance functor_category_has_colimits_of_size [has_colimits_of_size.{v₁, u₁} C] :
    has_colimits_of_size.{v₁, u₁} (K ⥤ C) :=
  ⟨inferInstance⟩

instance evaluation_preserves_limits_of_shape [has_limits_of_shape J C] (k : K) :
    preserves_limits_of_shape J ((evaluation K C).obj k) where
  PreservesLimit := fun F =>
    preserves_limit_of_preserves_limit_cone (combined_is_limit _ _) $
      is_limit.of_iso_limit (limit.is_limit _) (evaluate_combined_cones F _ k).symm

/-- If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a limit,
then the evaluation of that limit at `k` is the limit of the evaluations of `F.obj j` at `k`.
-/
def limit_obj_iso_limit_comp_evaluation [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (limit F).obj k ≅ limit (F ⋙ (evaluation K C).obj k) :=
  preserves_limit_iso ((evaluation K C).obj k) F

@[simp, reassoc]
theorem limit_obj_iso_limit_comp_evaluation_hom_π [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    (limit_obj_iso_limit_comp_evaluation F k).Hom ≫ limit.π (F ⋙ (evaluation K C).obj k) j = (limit.π F j).app k := by
  dsimp [limit_obj_iso_limit_comp_evaluation]
  simp

@[simp, reassoc]
theorem limit_obj_iso_limit_comp_evaluation_inv_π_app [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    (limit_obj_iso_limit_comp_evaluation F k).inv ≫ (limit.π F j).app k = limit.π (F ⋙ (evaluation K C).obj k) j := by
  dsimp [limit_obj_iso_limit_comp_evaluation]
  rw [iso.inv_comp_eq]
  simp

@[simp, reassoc]
theorem limit_map_limit_obj_iso_limit_comp_evaluation_hom [has_limits_of_shape J C] {i j : K} (F : J ⥤ K ⥤ C)
    (f : i ⟶ j) :
    (limit F).map f ≫ (limit_obj_iso_limit_comp_evaluation _ _).Hom =
      (limit_obj_iso_limit_comp_evaluation _ _).Hom ≫ lim_map (whisker_left _ ((evaluation _ _).map f)) :=
  by
  ext
  dsimp
  simp

@[simp, reassoc]
theorem limit_obj_iso_limit_comp_evaluation_inv_limit_map [has_limits_of_shape J C] {i j : K} (F : J ⥤ K ⥤ C)
    (f : i ⟶ j) :
    (limit_obj_iso_limit_comp_evaluation _ _).inv ≫ (limit F).map f =
      lim_map (whisker_left _ ((evaluation _ _).map f)) ≫ (limit_obj_iso_limit_comp_evaluation _ _).inv :=
  by
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv, limit_map_limit_obj_iso_limit_comp_evaluation_hom]

@[ext]
theorem limit_obj_ext {H : J ⥤ K ⥤ C} [has_limits_of_shape J C] {k : K} {W : C} {f g : W ⟶ (limit H).obj k}
    (w : ∀ j, f ≫ (limits.limit.π H j).app k = g ≫ (limits.limit.π H j).app k) : f = g := by
  apply (cancel_mono (limit_obj_iso_limit_comp_evaluation H k).Hom).1
  ext
  simpa using w j

instance evaluation_preserves_colimits_of_shape [has_colimits_of_shape J C] (k : K) :
    preserves_colimits_of_shape J ((evaluation K C).obj k) where
  PreservesColimit := fun F =>
    preserves_colimit_of_preserves_colimit_cocone (combined_is_colimit _ _) $
      is_colimit.of_iso_colimit (colimit.is_colimit _) (evaluate_combined_cocones F _ k).symm

/-- If `F : J ⥤ K ⥤ C` is a functor into a functor category which has a colimit,
then the evaluation of that colimit at `k` is the colimit of the evaluations of `F.obj j` at `k`.
-/
def colimit_obj_iso_colimit_comp_evaluation [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (k : K) :
    (colimit F).obj k ≅ colimit (F ⋙ (evaluation K C).obj k) :=
  preserves_colimit_iso ((evaluation K C).obj k) F

@[simp, reassoc]
theorem colimit_obj_iso_colimit_comp_evaluation_ι_inv [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    colimit.ι (F ⋙ (evaluation K C).obj k) j ≫ (colimit_obj_iso_colimit_comp_evaluation F k).inv =
      (colimit.ι F j).app k :=
  by
  dsimp [colimit_obj_iso_colimit_comp_evaluation]
  simp

@[simp, reassoc]
theorem colimit_obj_iso_colimit_comp_evaluation_ι_app_hom [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) (j : J) (k : K) :
    (colimit.ι F j).app k ≫ (colimit_obj_iso_colimit_comp_evaluation F k).Hom =
      colimit.ι (F ⋙ (evaluation K C).obj k) j :=
  by
  dsimp [colimit_obj_iso_colimit_comp_evaluation]
  rw [← iso.eq_comp_inv]
  simp

@[simp, reassoc]
theorem colimit_obj_iso_colimit_comp_evaluation_inv_colimit_map [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) {i j : K}
    (f : i ⟶ j) :
    (colimit_obj_iso_colimit_comp_evaluation _ _).inv ≫ (colimit F).map f =
      colim_map (whisker_left _ ((evaluation _ _).map f)) ≫ (colimit_obj_iso_colimit_comp_evaluation _ _).inv :=
  by
  ext
  dsimp
  simp

@[simp, reassoc]
theorem colimit_map_colimit_obj_iso_colimit_comp_evaluation_hom [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) {i j : K}
    (f : i ⟶ j) :
    (colimit F).map f ≫ (colimit_obj_iso_colimit_comp_evaluation _ _).Hom =
      (colimit_obj_iso_colimit_comp_evaluation _ _).Hom ≫ colim_map (whisker_left _ ((evaluation _ _).map f)) :=
  by
  rw [← iso.inv_comp_eq, ← category.assoc, ← iso.eq_comp_inv, colimit_obj_iso_colimit_comp_evaluation_inv_colimit_map]

@[ext]
theorem colimit_obj_ext {H : J ⥤ K ⥤ C} [has_colimits_of_shape J C] {k : K} {W : C} {f g : (colimit H).obj k ⟶ W}
    (w : ∀ j, (colimit.ι H j).app k ≫ f = (colimit.ι H j).app k ≫ g) : f = g := by
  apply (cancel_epi (colimit_obj_iso_colimit_comp_evaluation H k).inv).1
  ext
  simpa using w j

instance evaluation_preserves_limits [has_limits C] (k : K) : preserves_limits ((evaluation K C).obj k) where
  PreservesLimitsOfShape := fun J 𝒥 => by
    skip <;> infer_instance

/-- `F : D ⥤ K ⥤ C` preserves the limit of some `G : J ⥤ D` if it does for each `k : K`. -/
def preserves_limit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : ∀ k : K, preserves_limit G (F ⋙ (evaluation K C).obj k : D ⥤ C)) : preserves_limit G F :=
  ⟨fun c hc => by
    apply evaluation_jointly_reflects_limits
    intro X
    have := H X
    change is_limit ((F ⋙ (evaluation K C).obj X).mapCone c)
    exact preserves_limit.preserves hc⟩

/-- `F : D ⥤ K ⥤ C` preserves limits of shape `J` if it does for each `k : K`. -/
def preserves_limits_of_shape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type _) [category J]
    (H : ∀ k : K, preserves_limits_of_shape J (F ⋙ (evaluation K C).obj k)) : preserves_limits_of_shape J F :=
  ⟨fun G => preserves_limit_of_evaluation F G fun k => preserves_limits_of_shape.preserves_limit⟩

/-- `F : D ⥤ K ⥤ C` preserves all limits if it does for each `k : K`. -/
def preserves_limits_of_evaluation.{w', w} (F : D ⥤ K ⥤ C)
    (H : ∀ k : K, preserves_limits_of_size.{w', w} (F ⋙ (evaluation K C).obj k)) : preserves_limits_of_size.{w', w} F :=
  ⟨fun L hL => preserves_limits_of_shape_of_evaluation F L fun k => preserves_limits_of_size.preserves_limits_of_shape⟩

instance evaluation_preserves_colimits [has_colimits C] (k : K) : preserves_colimits ((evaluation K C).obj k) where
  PreservesColimitsOfShape := fun J 𝒥 => by
    skip <;> infer_instance

/-- `F : D ⥤ K ⥤ C` preserves the colimit of some `G : J ⥤ D` if it does for each `k : K`. -/
def preserves_colimit_of_evaluation (F : D ⥤ K ⥤ C) (G : J ⥤ D)
    (H : ∀ k, preserves_colimit G (F ⋙ (evaluation K C).obj k)) : preserves_colimit G F :=
  ⟨fun c hc => by
    apply evaluation_jointly_reflects_colimits
    intro X
    have := H X
    change is_colimit ((F ⋙ (evaluation K C).obj X).mapCocone c)
    exact preserves_colimit.preserves hc⟩

/-- `F : D ⥤ K ⥤ C` preserves all colimits of shape `J` if it does for each `k : K`. -/
def preserves_colimits_of_shape_of_evaluation (F : D ⥤ K ⥤ C) (J : Type _) [category J]
    (H : ∀ k : K, preserves_colimits_of_shape J (F ⋙ (evaluation K C).obj k)) : preserves_colimits_of_shape J F :=
  ⟨fun G => preserves_colimit_of_evaluation F G fun k => preserves_colimits_of_shape.preserves_colimit⟩

/-- `F : D ⥤ K ⥤ C` preserves all colimits if it does for each `k : K`. -/
def preserves_colimits_of_evaluation.{w', w} (F : D ⥤ K ⥤ C)
    (H : ∀ k : K, preserves_colimits_of_size.{w', w} (F ⋙ (evaluation K C).obj k)) :
    preserves_colimits_of_size.{w', w} F :=
  ⟨fun L hL =>
    preserves_colimits_of_shape_of_evaluation F L fun k => preserves_colimits_of_size.preserves_colimits_of_shape⟩

open CategoryTheory.prod

/-- The limit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual limits on objects. -/
@[simps]
def limit_iso_flip_comp_lim [has_limits_of_shape J C] (F : J ⥤ K ⥤ C) : limit F ≅ F.flip ⋙ lim :=
  nat_iso.of_components (limit_obj_iso_limit_comp_evaluation F) $ by
    tidy

/-- A variant of `limit_iso_flip_comp_lim` where the arguemnts of `F` are flipped. -/
@[simps]
def limit_flip_iso_comp_lim [has_limits_of_shape J C] (F : K ⥤ J ⥤ C) : limit F.flip ≅ F ⋙ lim :=
  (nat_iso.of_components fun k =>
      limit_obj_iso_limit_comp_evaluation F.flip k ≪≫ has_limit.iso_of_nat_iso (flip_comp_evaluation _ _)) $
    by
    tidy

/-- For a functor `G : J ⥤ K ⥤ C`, its limit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ lim`.
Note that this does not require `K` to be small.
-/
@[simps]
def limit_iso_swap_comp_lim [has_limits_of_shape J C] (G : J ⥤ K ⥤ C) :
    limit G ≅ curry.obj (swap K J ⋙ uncurry.obj G) ⋙ lim :=
  limit_iso_flip_comp_lim G ≪≫ iso_whisker_right (flip_iso_curry_swap_uncurry _) _

/-- The colimit of a diagram `F : J ⥤ K ⥤ C` is isomorphic to the functor given by
the individual colimits on objects. -/
@[simps]
def colimit_iso_flip_comp_colim [has_colimits_of_shape J C] (F : J ⥤ K ⥤ C) : colimit F ≅ F.flip ⋙ colim :=
  nat_iso.of_components (colimit_obj_iso_colimit_comp_evaluation F) $ by
    tidy

/-- A variant of `colimit_iso_flip_comp_colim` where the arguemnts of `F` are flipped. -/
@[simps]
def colimit_flip_iso_comp_colim [has_colimits_of_shape J C] (F : K ⥤ J ⥤ C) : colimit F.flip ≅ F ⋙ colim :=
  (nat_iso.of_components fun k =>
      colimit_obj_iso_colimit_comp_evaluation _ _ ≪≫ has_colimit.iso_of_nat_iso (flip_comp_evaluation _ _)) $
    by
    tidy

/-- For a functor `G : J ⥤ K ⥤ C`, its colimit `K ⥤ C` is given by `(G' : K ⥤ J ⥤ C) ⋙ colim`.
Note that this does not require `K` to be small.
-/
@[simps]
def colimit_iso_swap_comp_colim [has_colimits_of_shape J C] (G : J ⥤ K ⥤ C) :
    colimit G ≅ curry.obj (swap K J ⋙ uncurry.obj G) ⋙ colim :=
  colimit_iso_flip_comp_colim G ≪≫ iso_whisker_right (flip_iso_curry_swap_uncurry _) _

end CategoryTheory.Limits

