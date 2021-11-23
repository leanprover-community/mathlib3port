import Mathbin.CategoryTheory.Limits.IsLimit

/-!
# Existence of limits and colimits

In `category_theory.limits.is_limit` we defined `is_limit c`,
the data showing that a cone `c` is a limit cone.

The two main structures defined in this file are:
* `limit_cone F`, which consists of a choice of cone for `F` and the fact it is a limit cone, and
* `has_limit F`, asserting the mere existence of some limit cone for `F`.

`has_limit` is a propositional typeclass
(it's important that it is a proposition merely asserting the existence of a limit,
as otherwise we would have non-defeq problems from incompatible instances).

While `has_limit` only asserts the existence of a limit cone,
we happily use the axiom of choice in mathlib,
so there are convenience functions all depending on `has_limit F`:
* `limit F : C`, producing some limit object (of course all such are isomorphic)
* `limit.π F j : limit F ⟶ F.obj j`, the morphisms out of the limit,
* `limit.lift F c : c.X ⟶ limit F`, the universal morphism from any other `c : cone F`, etc.

Key to using the `has_limit` interface is that there is an `@[ext]` lemma stating that
to check `f = g`, for `f g : Z ⟶ limit F`, it suffices to check `f ≫ limit.π F j = g ≫ limit.π F j`
for every `j`.
This, combined with `@[simp]` lemmas, makes it possible to prove many easy facts about limits using
automation (e.g. `tidy`).

There are abbreviations `has_limits_of_shape J C` and `has_limits C`
asserting the existence of classes of limits.
Later more are introduced, for finite limits, special shapes of limits, etc.

Ideally, many results about limits should be stated first in terms of `is_limit`,
and then a result in terms of `has_limit` derived from this.
At this point, however, this is far from uniformly achieved in mathlib ---
often statements are only written in terms of `has_limit`.

## Implementation
At present we simply say everything twice, in order to handle both limits and colimits.
It would be highly desirable to have some automation support,
e.g. a `@[dualize]` attribute that behaves similarly to `@[to_additive]`.

## References
* [Stacks: Limits and colimits](https://stacks.math.columbia.edu/tag/002D)

-/


noncomputable theory

open CategoryTheory CategoryTheory.Category CategoryTheory.Functor Opposite

namespace CategoryTheory.Limits

universe v u u' u'' w

variable{J K : Type v}[small_category J][small_category K]

variable{C : Type u}[category.{v} C]

variable{F : J ⥤ C}

section Limit

/-- `limit_cone F` contains a cone over `F` together with the information that it is a limit. -/
@[nolint has_inhabited_instance]
structure limit_cone(F : J ⥤ C) where 
  Cone : cone F 
  IsLimit : is_limit cone

/-- `has_limit F` represents the mere existence of a limit for `F`. -/
class has_limit(F : J ⥤ C) : Prop where mk' :: 
  exists_limit : Nonempty (limit_cone F)

theorem has_limit.mk {F : J ⥤ C} (d : limit_cone F) : has_limit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `limit_cone F` from `has_limit F`. -/
def get_limit_cone (F : J ⥤ C) [has_limit F] : limit_cone F :=
  Classical.choice$ has_limit.exists_limit

variable(J C)

/-- `C` has limits of shape `J` if there exists a limit for every functor `F : J ⥤ C`. -/
class has_limits_of_shape : Prop where 
  HasLimit : ∀ F : J ⥤ C, has_limit F :=  by 
  runTac 
    tactic.apply_instance

/-- `C` has all (small) limits if it has limits of every shape. -/
class has_limits : Prop where 
  HasLimitsOfShape : ∀ J : Type v [𝒥 : small_category J], has_limits_of_shape J C :=  by 
  runTac 
    tactic.apply_instance

variable{J C}

instance (priority := 100)has_limit_of_has_limits_of_shape {J : Type v} [small_category J] [H : has_limits_of_shape J C]
  (F : J ⥤ C) : has_limit F :=
  has_limits_of_shape.has_limit F

instance (priority := 100)has_limits_of_shape_of_has_limits {J : Type v} [small_category J] [H : has_limits C] :
  has_limits_of_shape J C :=
  has_limits.has_limits_of_shape J

/-- An arbitrary choice of limit cone for a functor. -/
def limit.cone (F : J ⥤ C) [has_limit F] : cone F :=
  (get_limit_cone F).Cone

/-- An arbitrary choice of limit object of a functor. -/
def limit (F : J ⥤ C) [has_limit F] :=
  (limit.cone F).x

/-- The projection from the limit object to a value of the functor. -/
def limit.π (F : J ⥤ C) [has_limit F] (j : J) : limit F ⟶ F.obj j :=
  (limit.cone F).π.app j

@[simp]
theorem limit.cone_X {F : J ⥤ C} [has_limit F] : (limit.cone F).x = limit F :=
  rfl

@[simp]
theorem limit.cone_π {F : J ⥤ C} [has_limit F] : (limit.cone F).π.app = limit.π _ :=
  rfl

@[simp, reassoc]
theorem limit.w (F : J ⥤ C) [has_limit F] {j j' : J} (f : j ⟶ j') : limit.π F j ≫ F.map f = limit.π F j' :=
  (limit.cone F).w f

/-- Evidence that the arbitrary choice of cone provied by `limit.cone F` is a limit cone. -/
def limit.is_limit (F : J ⥤ C) [has_limit F] : is_limit (limit.cone F) :=
  (get_limit_cone F).IsLimit

/-- The morphism from the cone point of any other cone to the limit object. -/
def limit.lift (F : J ⥤ C) [has_limit F] (c : cone F) : c.X ⟶ limit F :=
  (limit.is_limit F).lift c

@[simp]
theorem limit.is_limit_lift {F : J ⥤ C} [has_limit F] (c : cone F) : (limit.is_limit F).lift c = limit.lift F c :=
  rfl

@[simp, reassoc]
theorem limit.lift_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) : limit.lift F c ≫ limit.π F j = c.π.app j :=
  is_limit.fac _ c j

/--
Functoriality of limits.

Usually this morphism should be accessed through `lim.map`,
but may be needed separately when you have specified limits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def lim_map {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) : limit F ⟶ limit G :=
  is_limit.map _ (limit.is_limit G) α

@[simp, reassoc]
theorem lim_map_π {F G : J ⥤ C} [has_limit F] [has_limit G] (α : F ⟶ G) (j : J) :
  lim_map α ≫ limit.π G j = limit.π F j ≫ α.app j :=
  limit.lift_π _ j

/-- The cone morphism from any cone to the arbitrary choice of limit cone. -/
def limit.cone_morphism {F : J ⥤ C} [has_limit F] (c : cone F) : c ⟶ limit.cone F :=
  (limit.is_limit F).liftConeMorphism c

@[simp]
theorem limit.cone_morphism_hom {F : J ⥤ C} [has_limit F] (c : cone F) : (limit.cone_morphism c).Hom = limit.lift F c :=
  rfl

theorem limit.cone_morphism_π {F : J ⥤ C} [has_limit F] (c : cone F) (j : J) :
  (limit.cone_morphism c).Hom ≫ limit.π F j = c.π.app j :=
  by 
    simp 

@[simp, reassoc]
theorem limit.cone_point_unique_up_to_iso_hom_comp {F : J ⥤ C} [has_limit F] {c : cone F} (hc : is_limit c) (j : J) :
  (is_limit.cone_point_unique_up_to_iso hc (limit.is_limit _)).Hom ≫ limit.π F j = c.π.app j :=
  is_limit.cone_point_unique_up_to_iso_hom_comp _ _ _

@[simp, reassoc]
theorem limit.cone_point_unique_up_to_iso_inv_comp {F : J ⥤ C} [has_limit F] {c : cone F} (hc : is_limit c) (j : J) :
  (is_limit.cone_point_unique_up_to_iso (limit.is_limit _) hc).inv ≫ limit.π F j = c.π.app j :=
  is_limit.cone_point_unique_up_to_iso_inv_comp _ _ _

/--
Given any other limit cone for `F`, the chosen `limit F` is isomorphic to the cone point.
-/
def limit.iso_limit_cone {F : J ⥤ C} [has_limit F] (t : limit_cone F) : limit F ≅ t.cone.X :=
  is_limit.cone_point_unique_up_to_iso (limit.is_limit F) t.is_limit

@[simp, reassoc]
theorem limit.iso_limit_cone_hom_π {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) :
  (limit.iso_limit_cone t).Hom ≫ t.cone.π.app j = limit.π F j :=
  by 
    dsimp [limit.iso_limit_cone, is_limit.cone_point_unique_up_to_iso]
    tidy

@[simp, reassoc]
theorem limit.iso_limit_cone_inv_π {F : J ⥤ C} [has_limit F] (t : limit_cone F) (j : J) :
  (limit.iso_limit_cone t).inv ≫ limit.π F j = t.cone.π.app j :=
  by 
    dsimp [limit.iso_limit_cone, is_limit.cone_point_unique_up_to_iso]
    tidy

@[ext]
theorem limit.hom_ext {F : J ⥤ C} [has_limit F] {X : C} {f f' : X ⟶ limit F}
  (w : ∀ j, f ≫ limit.π F j = f' ≫ limit.π F j) : f = f' :=
  (limit.is_limit F).hom_ext w

@[simp]
theorem limit.lift_map {F G : J ⥤ C} [has_limit F] [has_limit G] (c : cone F) (α : F ⟶ G) :
  limit.lift F c ≫ lim_map α = limit.lift G ((cones.postcompose α).obj c) :=
  by 
    ext 
    rw [assoc, lim_map_π, limit.lift_π_assoc, limit.lift_π]
    rfl

@[simp]
theorem limit.lift_cone {F : J ⥤ C} [has_limit F] : limit.lift F (limit.cone F) = 𝟙 (limit F) :=
  (limit.is_limit _).lift_self

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and cones with cone point `W`.
-/
def limit.hom_iso (F : J ⥤ C) [has_limit F] (W : C) : (W ⟶ limit F) ≅ F.cones.obj (op W) :=
  (limit.is_limit F).homIso W

@[simp]
theorem limit.hom_iso_hom (F : J ⥤ C) [has_limit F] {W : C} (f : W ⟶ limit F) :
  (limit.hom_iso F W).Hom f = (const J).map f ≫ (limit.cone F).π :=
  (limit.is_limit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from a specified object `W` to the limit object,
and an explicit componentwise description of cones with cone point `W`.
-/
def limit.hom_iso' (F : J ⥤ C) [has_limit F] (W : C) :
  (W ⟶ limit F : Type v) ≅ { p : ∀ j, W ⟶ F.obj j // ∀ {j j' : J} f : j ⟶ j', p j ≫ F.map f = p j' } :=
  (limit.is_limit F).homIso' W

theorem limit.lift_extend {F : J ⥤ C} [has_limit F] (c : cone F) {X : C} (f : X ⟶ c.X) :
  limit.lift F (c.extend f) = f ≫ limit.lift F c :=
  by 
    runTac 
      obviously

/--
If a functor `F` has a limit, so does any naturally isomorphic functor.
-/
theorem has_limit_of_iso {F G : J ⥤ C} [has_limit F] (α : F ≅ G) : has_limit G :=
  has_limit.mk
    { Cone := (cones.postcompose α.hom).obj (limit.cone F),
      IsLimit :=
        { lift := fun s => limit.lift F ((cones.postcompose α.inv).obj s),
          fac' :=
            fun s j =>
              by 
                rw [cones.postcompose_obj_π, nat_trans.comp_app, limit.cone_π, ←category.assoc, limit.lift_π]
                simp ,
          uniq' :=
            fun s m w =>
              by 
                apply limit.hom_ext 
                intro j 
                rw [limit.lift_π, cones.postcompose_obj_π, nat_trans.comp_app, ←nat_iso.app_inv, iso.eq_comp_inv]
                simpa using w j } }

/-- If a functor `G` has the same collection of cones as a functor `F`
which has a limit, then `G` also has a limit. -/
theorem has_limit.of_cones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cones ≅ G.cones) [has_limit F] : has_limit G :=
  has_limit.mk ⟨_, is_limit.of_nat_iso (is_limit.nat_iso (limit.is_limit F) ≪≫ h)⟩

/--
The limits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_limit.iso_of_nat_iso {F G : J ⥤ C} [has_limit F] [has_limit G] (w : F ≅ G) : limit F ≅ limit G :=
  is_limit.cone_points_iso_of_nat_iso (limit.is_limit F) (limit.is_limit G) w

@[simp, reassoc]
theorem has_limit.iso_of_nat_iso_hom_π {F G : J ⥤ C} [has_limit F] [has_limit G] (w : F ≅ G) (j : J) :
  (has_limit.iso_of_nat_iso w).Hom ≫ limit.π G j = limit.π F j ≫ w.hom.app j :=
  is_limit.cone_points_iso_of_nat_iso_hom_comp _ _ _ _

@[simp, reassoc]
theorem has_limit.lift_iso_of_nat_iso_hom {F G : J ⥤ C} [has_limit F] [has_limit G] (t : cone F) (w : F ≅ G) :
  limit.lift F t ≫ (has_limit.iso_of_nat_iso w).Hom = limit.lift G ((cones.postcompose w.hom).obj _) :=
  is_limit.lift_comp_cone_points_iso_of_nat_iso_hom _ _ _

/--
The limits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_limit.iso_of_equivalence {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G] (e : J ≌ K)
  (w : e.functor ⋙ G ≅ F) : limit F ≅ limit G :=
  is_limit.cone_points_iso_of_equivalence (limit.is_limit F) (limit.is_limit G) e w

@[simp]
theorem has_limit.iso_of_equivalence_hom_π {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G] (e : J ≌ K)
  (w : e.functor ⋙ G ≅ F) (k : K) :
  (has_limit.iso_of_equivalence e w).Hom ≫ limit.π G k =
    limit.π F (e.inverse.obj k) ≫ w.inv.app (e.inverse.obj k) ≫ G.map (e.counit.app k) :=
  by 
    simp only [has_limit.iso_of_equivalence, is_limit.cone_points_iso_of_equivalence_hom]
    dsimp 
    simp 

@[simp]
theorem has_limit.iso_of_equivalence_inv_π {F : J ⥤ C} [has_limit F] {G : K ⥤ C} [has_limit G] (e : J ≌ K)
  (w : e.functor ⋙ G ≅ F) (j : J) :
  (has_limit.iso_of_equivalence e w).inv ≫ limit.π F j = limit.π G (e.functor.obj j) ≫ w.hom.app j :=
  by 
    simp only [has_limit.iso_of_equivalence, is_limit.cone_points_iso_of_equivalence_hom]
    dsimp 
    simp 

section Pre

variable(F)[has_limit F](E : K ⥤ J)[has_limit (E ⋙ F)]

/--
The canonical morphism from the limit of `F` to the limit of `E ⋙ F`.
-/
def limit.pre : limit F ⟶ limit (E ⋙ F) :=
  limit.lift (E ⋙ F) ((limit.cone F).whisker E)

@[simp, reassoc]
theorem limit.pre_π (k : K) : limit.pre F E ≫ limit.π (E ⋙ F) k = limit.π F (E.obj k) :=
  by 
    erw [is_limit.fac]
    rfl

@[simp]
theorem limit.lift_pre (c : cone F) : limit.lift F c ≫ limit.pre F E = limit.lift (E ⋙ F) (c.whisker E) :=
  by 
    ext <;> simp 

variable{L : Type v}[small_category L]

variable(D : L ⥤ K)[has_limit (D ⋙ E ⋙ F)]

@[simp]
theorem limit.pre_pre : limit.pre F E ≫ limit.pre (E ⋙ F) D = limit.pre F (D ⋙ E) :=
  by 
    ext j <;> erw [assoc, limit.pre_π, limit.pre_π, limit.pre_π] <;> rfl

variable{E F}

/---
If we have particular limit cones available for `E ⋙ F` and for `F`,
we obtain a formula for `limit.pre F E`.
-/
theorem limit.pre_eq (s : limit_cone (E ⋙ F)) (t : limit_cone F) :
  limit.pre F E = (limit.iso_limit_cone t).Hom ≫ s.is_limit.lift (t.cone.whisker E) ≫ (limit.iso_limit_cone s).inv :=
  by 
    tidy

end Pre

section Post

variable{D : Type u'}[category.{v} D]

variable(F)[has_limit F](G : C ⥤ D)[has_limit (F ⋙ G)]

/--
The canonical morphism from `G` applied to the limit of `F` to the limit of `F ⋙ G`.
-/
def limit.post : G.obj (limit F) ⟶ limit (F ⋙ G) :=
  limit.lift (F ⋙ G) (G.map_cone (limit.cone F))

@[simp, reassoc]
theorem limit.post_π (j : J) : limit.post F G ≫ limit.π (F ⋙ G) j = G.map (limit.π F j) :=
  by 
    erw [is_limit.fac]
    rfl

@[simp]
theorem limit.lift_post (c : cone F) : G.map (limit.lift F c) ≫ limit.post F G = limit.lift (F ⋙ G) (G.map_cone c) :=
  by 
    ext 
    rw [assoc, limit.post_π, ←G.map_comp, limit.lift_π, limit.lift_π]
    rfl

@[simp]
theorem limit.post_post {E : Type u''} [category.{v} E] (H : D ⥤ E) [has_limit ((F ⋙ G) ⋙ H)] :
  H.map (limit.post F G) ≫ limit.post (F ⋙ G) H = limit.post F (G ⋙ H) :=
  by 
    ext <;> erw [assoc, limit.post_π, ←H.map_comp, limit.post_π, limit.post_π] <;> rfl

end Post

theorem limit.pre_post {D : Type u'} [category.{v} D] (E : K ⥤ J) (F : J ⥤ C) (G : C ⥤ D) [has_limit F]
  [has_limit (E ⋙ F)] [has_limit (F ⋙ G)] [has_limit ((E ⋙ F) ⋙ G)] :
  G.map (limit.pre F E) ≫ limit.post (E ⋙ F) G = limit.post F G ≫ limit.pre (F ⋙ G) E :=
  by 
    ext <;> erw [assoc, limit.post_π, ←G.map_comp, limit.pre_π, assoc, limit.pre_π, limit.post_π] <;> rfl

open CategoryTheory.Equivalence

instance has_limit_equivalence_comp (e : K ≌ J) [has_limit F] : has_limit (e.functor ⋙ F) :=
  has_limit.mk
    { Cone := cone.whisker e.functor (limit.cone F), IsLimit := is_limit.whisker_equivalence (limit.is_limit F) e }

attribute [local elabWithoutExpectedType] inv_fun_id_assoc

-- error in CategoryTheory.Limits.HasLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If a `E ⋙ F` has a limit, and `E` is an equivalence, we can construct a limit of `F`.
-/ theorem has_limit_of_equivalence_comp (e : «expr ≌ »(K, J)) [has_limit «expr ⋙ »(e.functor, F)] : has_limit F :=
begin
  haveI [] [":", expr has_limit «expr ⋙ »(e.inverse, «expr ⋙ »(e.functor, F))] [":=", expr limits.has_limit_equivalence_comp e.symm],
  apply [expr has_limit_of_iso (e.inv_fun_id_assoc F)]
end

section LimFunctor

variable[has_limits_of_shape J C]

section 

/-- `limit F` is functorial in `F`, when `C` has all limits of shape `J`. -/
@[simps obj]
def lim : (J ⥤ C) ⥤ C :=
  { obj := fun F => limit F, map := fun F G α => lim_map α,
    map_id' :=
      fun F =>
        by 
          ext 
          erw [lim_map_π, category.id_comp, category.comp_id],
    map_comp' :=
      fun F G H α β =>
        by 
          ext <;> erw [assoc, is_limit.fac, is_limit.fac, ←assoc, is_limit.fac, assoc] <;> rfl }

end 

variable{F}{G : J ⥤ C}(α : F ⟶ G)

@[simp]
theorem lim_map_eq_lim_map : lim.map α = lim_map α :=
  rfl

theorem limit.map_pre [has_limits_of_shape K C] (E : K ⥤ J) :
  lim.map α ≫ limit.pre G E = limit.pre F E ≫ lim.map (whisker_left E α) :=
  by 
    ext 
    simp 

theorem limit.map_pre' [has_limits_of_shape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  limit.pre F E₂ = limit.pre F E₁ ≫ lim.map (whisker_right α F) :=
  by 
    ext1 <;> simp [←category.assoc]

theorem limit.id_pre (F : J ⥤ C) : limit.pre F (𝟭 _) = lim.map (functor.left_unitor F).inv :=
  by 
    tidy

theorem limit.map_post {D : Type u'} [category.{v} D] [has_limits_of_shape J D] (H : C ⥤ D) :
  H.map (lim_map α) ≫ limit.post G H = limit.post F H ≫ lim_map (whisker_right α H) :=
  by 
    ext 
    simp only [whisker_right_app, lim_map_π, assoc, limit.post_π_assoc, limit.post_π, ←H.map_comp]

/--
The isomorphism between
morphisms from `W` to the cone point of the limit cone for `F`
and cones over `F` with cone point `W`
is natural in `F`.
-/
def lim_yoneda : lim ⋙ yoneda ≅ CategoryTheory.cones J C :=
  nat_iso.of_components
    (fun F =>
      nat_iso.of_components (fun W => limit.hom_iso F (unop W))
        (by 
          tidy))
    (by 
      tidy)

end LimFunctor

/--
We can transport limits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem has_limits_of_shape_of_equivalence {J' : Type v} [small_category J'] (e : J ≌ J') [has_limits_of_shape J C] :
  has_limits_of_shape J' C :=
  by 
    constructor 
    intro F 
    apply has_limit_of_equivalence_comp e 
    infer_instance

end Limit

section Colimit

/-- `colimit_cocone F` contains a cocone over `F` together with the information that it is a
    colimit. -/
@[nolint has_inhabited_instance]
structure colimit_cocone(F : J ⥤ C) where 
  Cocone : cocone F 
  IsColimit : is_colimit cocone

/-- `has_colimit F` represents the mere existence of a colimit for `F`. -/
class has_colimit(F : J ⥤ C) : Prop where mk' :: 
  exists_colimit : Nonempty (colimit_cocone F)

theorem has_colimit.mk {F : J ⥤ C} (d : colimit_cocone F) : has_colimit F :=
  ⟨Nonempty.intro d⟩

/-- Use the axiom of choice to extract explicit `colimit_cocone F` from `has_colimit F`. -/
def get_colimit_cocone (F : J ⥤ C) [has_colimit F] : colimit_cocone F :=
  Classical.choice$ has_colimit.exists_colimit

variable(J C)

/-- `C` has colimits of shape `J` if there exists a colimit for every functor `F : J ⥤ C`. -/
class has_colimits_of_shape : Prop where 
  HasColimit : ∀ F : J ⥤ C, has_colimit F :=  by 
  runTac 
    tactic.apply_instance

/-- `C` has all (small) colimits if it has colimits of every shape. -/
class has_colimits : Prop where 
  HasColimitsOfShape : ∀ J : Type v [𝒥 : small_category J], has_colimits_of_shape J C :=  by 
  runTac 
    tactic.apply_instance

variable{J C}

instance (priority := 100)has_colimit_of_has_colimits_of_shape {J : Type v} [small_category J]
  [H : has_colimits_of_shape J C] (F : J ⥤ C) : has_colimit F :=
  has_colimits_of_shape.has_colimit F

instance (priority := 100)has_colimits_of_shape_of_has_colimits {J : Type v} [small_category J] [H : has_colimits C] :
  has_colimits_of_shape J C :=
  has_colimits.has_colimits_of_shape J

/-- An arbitrary choice of colimit cocone of a functor. -/
def colimit.cocone (F : J ⥤ C) [has_colimit F] : cocone F :=
  (get_colimit_cocone F).Cocone

/-- An arbitrary choice of colimit object of a functor. -/
def colimit (F : J ⥤ C) [has_colimit F] :=
  (colimit.cocone F).x

/-- The coprojection from a value of the functor to the colimit object. -/
def colimit.ι (F : J ⥤ C) [has_colimit F] (j : J) : F.obj j ⟶ colimit F :=
  (colimit.cocone F).ι.app j

@[simp]
theorem colimit.cocone_ι {F : J ⥤ C} [has_colimit F] (j : J) : (colimit.cocone F).ι.app j = colimit.ι _ j :=
  rfl

@[simp]
theorem colimit.cocone_X {F : J ⥤ C} [has_colimit F] : (colimit.cocone F).x = colimit F :=
  rfl

@[simp, reassoc]
theorem colimit.w (F : J ⥤ C) [has_colimit F] {j j' : J} (f : j ⟶ j') : F.map f ≫ colimit.ι F j' = colimit.ι F j :=
  (colimit.cocone F).w f

/-- Evidence that the arbitrary choice of cocone is a colimit cocone. -/
def colimit.is_colimit (F : J ⥤ C) [has_colimit F] : is_colimit (colimit.cocone F) :=
  (get_colimit_cocone F).IsColimit

/-- The morphism from the colimit object to the cone point of any other cocone. -/
def colimit.desc (F : J ⥤ C) [has_colimit F] (c : cocone F) : colimit F ⟶ c.X :=
  (colimit.is_colimit F).desc c

@[simp]
theorem colimit.is_colimit_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.is_colimit F).desc c = colimit.desc F c :=
  rfl

/--
We have lots of lemmas describing how to simplify `colimit.ι F j ≫ _`,
and combined with `colimit.ext` we rely on these lemmas for many calculations.

However, since `category.assoc` is a `@[simp]` lemma, often expressions are
right associated, and it's hard to apply these lemmas about `colimit.ι`.

We thus use `reassoc` to define additional `@[simp]` lemmas, with an arbitrary extra morphism.
(see `tactic/reassoc_axiom.lean`)
 -/
@[simp, reassoc]
theorem colimit.ι_desc {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ colimit.desc F c = c.ι.app j :=
  is_colimit.fac _ c j

/--
Functoriality of colimits.

Usually this morphism should be accessed through `colim.map`,
but may be needed separately when you have specified colimits for the source and target functors,
but not necessarily for all functors of shape `J`.
-/
def colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) : colimit F ⟶ colimit G :=
  is_colimit.map (colimit.is_colimit F) _ α

@[simp, reassoc]
theorem ι_colim_map {F G : J ⥤ C} [has_colimit F] [has_colimit G] (α : F ⟶ G) (j : J) :
  colimit.ι F j ≫ colim_map α = α.app j ≫ colimit.ι G j :=
  colimit.ι_desc _ j

/-- The cocone morphism from the arbitrary choice of colimit cocone to any cocone. -/
def colimit.cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) : colimit.cocone F ⟶ c :=
  (colimit.is_colimit F).descCoconeMorphism c

@[simp]
theorem colimit.cocone_morphism_hom {F : J ⥤ C} [has_colimit F] (c : cocone F) :
  (colimit.cocone_morphism c).Hom = colimit.desc F c :=
  rfl

theorem colimit.ι_cocone_morphism {F : J ⥤ C} [has_colimit F] (c : cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.cocone_morphism c).Hom = c.ι.app j :=
  by 
    simp 

@[simp, reassoc]
theorem colimit.comp_cocone_point_unique_up_to_iso_hom {F : J ⥤ C} [has_colimit F] {c : cocone F} (hc : is_colimit c)
  (j : J) : colimit.ι F j ≫ (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _) hc).Hom = c.ι.app j :=
  is_colimit.comp_cocone_point_unique_up_to_iso_hom _ _ _

@[simp, reassoc]
theorem colimit.comp_cocone_point_unique_up_to_iso_inv {F : J ⥤ C} [has_colimit F] {c : cocone F} (hc : is_colimit c)
  (j : J) : colimit.ι F j ≫ (is_colimit.cocone_point_unique_up_to_iso hc (colimit.is_colimit _)).inv = c.ι.app j :=
  is_colimit.comp_cocone_point_unique_up_to_iso_inv _ _ _

/--
Given any other colimit cocone for `F`, the chosen `colimit F` is isomorphic to the cocone point.
-/
def colimit.iso_colimit_cocone {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) : colimit F ≅ t.cocone.X :=
  is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit F) t.is_colimit

@[simp, reassoc]
theorem colimit.iso_colimit_cocone_ι_hom {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) :
  colimit.ι F j ≫ (colimit.iso_colimit_cocone t).Hom = t.cocone.ι.app j :=
  by 
    dsimp [colimit.iso_colimit_cocone, is_colimit.cocone_point_unique_up_to_iso]
    tidy

@[simp, reassoc]
theorem colimit.iso_colimit_cocone_ι_inv {F : J ⥤ C} [has_colimit F] (t : colimit_cocone F) (j : J) :
  t.cocone.ι.app j ≫ (colimit.iso_colimit_cocone t).inv = colimit.ι F j :=
  by 
    dsimp [colimit.iso_colimit_cocone, is_colimit.cocone_point_unique_up_to_iso]
    tidy

@[ext]
theorem colimit.hom_ext {F : J ⥤ C} [has_colimit F] {X : C} {f f' : colimit F ⟶ X}
  (w : ∀ j, colimit.ι F j ≫ f = colimit.ι F j ≫ f') : f = f' :=
  (colimit.is_colimit F).hom_ext w

@[simp]
theorem colimit.desc_cocone {F : J ⥤ C} [has_colimit F] : colimit.desc F (colimit.cocone F) = 𝟙 (colimit F) :=
  (colimit.is_colimit _).desc_self

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and cocones with cone point `W`.
-/
def colimit.hom_iso (F : J ⥤ C) [has_colimit F] (W : C) : (colimit F ⟶ W) ≅ F.cocones.obj W :=
  (colimit.is_colimit F).homIso W

@[simp]
theorem colimit.hom_iso_hom (F : J ⥤ C) [has_colimit F] {W : C} (f : colimit F ⟶ W) :
  (colimit.hom_iso F W).Hom f = (colimit.cocone F).ι ≫ (const J).map f :=
  (colimit.is_colimit F).hom_iso_hom f

/--
The isomorphism (in `Type`) between
morphisms from the colimit object to a specified object `W`,
and an explicit componentwise description of cocones with cone point `W`.
-/
def colimit.hom_iso' (F : J ⥤ C) [has_colimit F] (W : C) :
  (colimit F ⟶ W : Type v) ≅ { p : ∀ j, F.obj j ⟶ W // ∀ {j j'} f : j ⟶ j', F.map f ≫ p j' = p j } :=
  (colimit.is_colimit F).homIso' W

theorem colimit.desc_extend (F : J ⥤ C) [has_colimit F] (c : cocone F) {X : C} (f : c.X ⟶ X) :
  colimit.desc F (c.extend f) = colimit.desc F c ≫ f :=
  by 
    ext1 
    rw [←category.assoc]
    simp 

/--
If `F` has a colimit, so does any naturally isomorphic functor.
-/
theorem has_colimit_of_iso {F G : J ⥤ C} [has_colimit F] (α : G ≅ F) : has_colimit G :=
  has_colimit.mk
    { Cocone := (cocones.precompose α.hom).obj (colimit.cocone F),
      IsColimit :=
        { desc := fun s => colimit.desc F ((cocones.precompose α.inv).obj s),
          fac' :=
            fun s j =>
              by 
                rw [cocones.precompose_obj_ι, nat_trans.comp_app, colimit.cocone_ι]
                rw [category.assoc, colimit.ι_desc, ←nat_iso.app_hom, ←iso.eq_inv_comp]
                rfl,
          uniq' :=
            fun s m w =>
              by 
                apply colimit.hom_ext 
                intro j 
                rw [colimit.ι_desc, cocones.precompose_obj_ι, nat_trans.comp_app, ←nat_iso.app_inv, iso.eq_inv_comp]
                simpa using w j } }

/-- If a functor `G` has the same collection of cocones as a functor `F`
which has a colimit, then `G` also has a colimit. -/
theorem has_colimit.of_cocones_iso {J K : Type v} [small_category J] [small_category K] (F : J ⥤ C) (G : K ⥤ C)
  (h : F.cocones ≅ G.cocones) [has_colimit F] : has_colimit G :=
  has_colimit.mk ⟨_, is_colimit.of_nat_iso (is_colimit.nat_iso (colimit.is_colimit F) ≪≫ h)⟩

/--
The colimits of `F : J ⥤ C` and `G : J ⥤ C` are isomorphic,
if the functors are naturally isomorphic.
-/
def has_colimit.iso_of_nat_iso {F G : J ⥤ C} [has_colimit F] [has_colimit G] (w : F ≅ G) : colimit F ≅ colimit G :=
  is_colimit.cocone_points_iso_of_nat_iso (colimit.is_colimit F) (colimit.is_colimit G) w

@[simp, reassoc]
theorem has_colimit.iso_of_nat_iso_ι_hom {F G : J ⥤ C} [has_colimit F] [has_colimit G] (w : F ≅ G) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_nat_iso w).Hom = w.hom.app j ≫ colimit.ι G j :=
  is_colimit.comp_cocone_points_iso_of_nat_iso_hom _ _ _ _

@[simp, reassoc]
theorem has_colimit.iso_of_nat_iso_hom_desc {F G : J ⥤ C} [has_colimit F] [has_colimit G] (t : cocone G) (w : F ≅ G) :
  (has_colimit.iso_of_nat_iso w).Hom ≫ colimit.desc G t = colimit.desc F ((cocones.precompose w.hom).obj _) :=
  is_colimit.cocone_points_iso_of_nat_iso_hom_desc _ _ _

/--
The colimits of `F : J ⥤ C` and `G : K ⥤ C` are isomorphic,
if there is an equivalence `e : J ≌ K` making the triangle commute up to natural isomorphism.
-/
def has_colimit.iso_of_equivalence {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G] (e : J ≌ K)
  (w : e.functor ⋙ G ≅ F) : colimit F ≅ colimit G :=
  is_colimit.cocone_points_iso_of_equivalence (colimit.is_colimit F) (colimit.is_colimit G) e w

@[simp]
theorem has_colimit.iso_of_equivalence_hom_π {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G] (e : J ≌ K)
  (w : e.functor ⋙ G ≅ F) (j : J) :
  colimit.ι F j ≫ (has_colimit.iso_of_equivalence e w).Hom = F.map (e.unit.app j) ≫ w.inv.app _ ≫ colimit.ι G _ :=
  by 
    simp [has_colimit.iso_of_equivalence, is_colimit.cocone_points_iso_of_equivalence_inv]
    dsimp 
    simp 

@[simp]
theorem has_colimit.iso_of_equivalence_inv_π {F : J ⥤ C} [has_colimit F] {G : K ⥤ C} [has_colimit G] (e : J ≌ K)
  (w : e.functor ⋙ G ≅ F) (k : K) :
  colimit.ι G k ≫ (has_colimit.iso_of_equivalence e w).inv =
    G.map (e.counit_inv.app k) ≫ w.hom.app (e.inverse.obj k) ≫ colimit.ι F (e.inverse.obj k) :=
  by 
    simp [has_colimit.iso_of_equivalence, is_colimit.cocone_points_iso_of_equivalence_inv]
    dsimp 
    simp 

section Pre

variable(F)[has_colimit F](E : K ⥤ J)[has_colimit (E ⋙ F)]

/--
The canonical morphism from the colimit of `E ⋙ F` to the colimit of `F`.
-/
def colimit.pre : colimit (E ⋙ F) ⟶ colimit F :=
  colimit.desc (E ⋙ F) ((colimit.cocone F).whisker E)

@[simp, reassoc]
theorem colimit.ι_pre (k : K) : colimit.ι (E ⋙ F) k ≫ colimit.pre F E = colimit.ι F (E.obj k) :=
  by 
    erw [is_colimit.fac]
    rfl

@[simp]
theorem colimit.pre_desc (c : cocone F) : colimit.pre F E ≫ colimit.desc F c = colimit.desc (E ⋙ F) (c.whisker E) :=
  by 
    ext <;> rw [←assoc, colimit.ι_pre] <;> simp 

variable{L : Type v}[small_category L]

variable(D : L ⥤ K)[has_colimit (D ⋙ E ⋙ F)]

-- error in CategoryTheory.Limits.HasLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[simp]
theorem colimit.pre_pre : «expr = »(«expr ≫ »(colimit.pre «expr ⋙ »(E, F) D, colimit.pre F E), colimit.pre F «expr ⋙ »(D, E)) :=
begin
  ext [] [ident j] [],
  rw ["[", "<-", expr assoc, ",", expr colimit.ι_pre, ",", expr colimit.ι_pre, "]"] [],
  letI [] [":", expr has_colimit «expr ⋙ »(«expr ⋙ »(D, E), F)] [":=", expr show has_colimit «expr ⋙ »(D, «expr ⋙ »(E, F)), by apply_instance],
  exact [expr (colimit.ι_pre F «expr ⋙ »(D, E) j).symm]
end

variable{E F}

/---
If we have particular colimit cocones available for `E ⋙ F` and for `F`,
we obtain a formula for `colimit.pre F E`.
-/
theorem colimit.pre_eq (s : colimit_cocone (E ⋙ F)) (t : colimit_cocone F) :
  colimit.pre F E =
    (colimit.iso_colimit_cocone s).Hom ≫ s.is_colimit.desc (t.cocone.whisker E) ≫ (colimit.iso_colimit_cocone t).inv :=
  by 
    tidy

end Pre

section Post

variable{D : Type u'}[category.{v} D]

variable(F)[has_colimit F](G : C ⥤ D)[has_colimit (F ⋙ G)]

/--
The canonical morphism from `G` applied to the colimit of `F ⋙ G`
to `G` applied to the colimit of `F`.
-/
def colimit.post : colimit (F ⋙ G) ⟶ G.obj (colimit F) :=
  colimit.desc (F ⋙ G) (G.map_cocone (colimit.cocone F))

@[simp, reassoc]
theorem colimit.ι_post (j : J) : colimit.ι (F ⋙ G) j ≫ colimit.post F G = G.map (colimit.ι F j) :=
  by 
    erw [is_colimit.fac]
    rfl

@[simp]
theorem colimit.post_desc (c : cocone F) :
  colimit.post F G ≫ G.map (colimit.desc F c) = colimit.desc (F ⋙ G) (G.map_cocone c) :=
  by 
    ext 
    rw [←assoc, colimit.ι_post, ←G.map_comp, colimit.ι_desc, colimit.ι_desc]
    rfl

@[simp]
theorem colimit.post_post {E : Type u''} [category.{v} E] (H : D ⥤ E) [has_colimit ((F ⋙ G) ⋙ H)] :
  colimit.post (F ⋙ G) H ≫ H.map (colimit.post F G) = colimit.post F (G ⋙ H) :=
  by 
    ext 
    rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_post]
    exact (colimit.ι_post F (G ⋙ H) j).symm

end Post

-- error in CategoryTheory.Limits.HasLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem colimit.pre_post
{D : Type u'}
[category.{v} D]
(E : «expr ⥤ »(K, J))
(F : «expr ⥤ »(J, C))
(G : «expr ⥤ »(C, D))
[has_colimit F]
[has_colimit «expr ⋙ »(E, F)]
[has_colimit «expr ⋙ »(F, G)]
[has_colimit «expr ⋙ »(«expr ⋙ »(E, F), G)] : «expr = »(«expr ≫ »(colimit.post «expr ⋙ »(E, F) G, G.map (colimit.pre F E)), «expr ≫ »(colimit.pre «expr ⋙ »(F, G) E, colimit.post F G)) :=
begin
  ext [] [] [],
  rw ["[", "<-", expr assoc, ",", expr colimit.ι_post, ",", "<-", expr G.map_comp, ",", expr colimit.ι_pre, ",", "<-", expr assoc, "]"] [],
  letI [] [":", expr has_colimit «expr ⋙ »(E, «expr ⋙ »(F, G))] [":=", expr show has_colimit «expr ⋙ »(«expr ⋙ »(E, F), G), by apply_instance],
  erw ["[", expr colimit.ι_pre «expr ⋙ »(F, G) E j, ",", expr colimit.ι_post, "]"] []
end

open CategoryTheory.Equivalence

instance has_colimit_equivalence_comp (e : K ≌ J) [has_colimit F] : has_colimit (e.functor ⋙ F) :=
  has_colimit.mk
    { Cocone := cocone.whisker e.functor (colimit.cocone F),
      IsColimit := is_colimit.whisker_equivalence (colimit.is_colimit F) e }

-- error in CategoryTheory.Limits.HasLimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
If a `E ⋙ F` has a colimit, and `E` is an equivalence, we can construct a colimit of `F`.
-/
theorem has_colimit_of_equivalence_comp (e : «expr ≌ »(K, J)) [has_colimit «expr ⋙ »(e.functor, F)] : has_colimit F :=
begin
  haveI [] [":", expr has_colimit «expr ⋙ »(e.inverse, «expr ⋙ »(e.functor, F))] [":=", expr limits.has_colimit_equivalence_comp e.symm],
  apply [expr has_colimit_of_iso (e.inv_fun_id_assoc F).symm]
end

section ColimFunctor

variable[has_colimits_of_shape J C]

section 

attribute [local simp] colim_map

/-- `colimit F` is functorial in `F`, when `C` has all colimits of shape `J`. -/
@[simps obj]
def colim : (J ⥤ C) ⥤ C :=
  { obj := fun F => colimit F, map := fun F G α => colim_map α,
    map_id' :=
      fun F =>
        by 
          ext 
          erw [ι_colim_map, id_comp, comp_id],
    map_comp' :=
      fun F G H α β =>
        by 
          ext 
          erw [←assoc, is_colimit.fac, is_colimit.fac, assoc, is_colimit.fac, ←assoc]
          rfl }

end 

variable{F}{G : J ⥤ C}(α : F ⟶ G)

@[simp, reassoc]
theorem colimit.ι_map (j : J) : colimit.ι F j ≫ colim.map α = α.app j ≫ colimit.ι G j :=
  by 
    apply is_colimit.fac

@[simp]
theorem colimit.map_desc (c : cocone G) :
  colim.map α ≫ colimit.desc G c = colimit.desc F ((cocones.precompose α).obj c) :=
  by 
    ext <;> rw [←assoc, colimit.ι_map, assoc, colimit.ι_desc, colimit.ι_desc] <;> rfl

theorem colimit.pre_map [has_colimits_of_shape K C] (E : K ⥤ J) :
  colimit.pre F E ≫ colim.map α = colim.map (whisker_left E α) ≫ colimit.pre G E :=
  by 
    ext <;> rw [←assoc, colimit.ι_pre, colimit.ι_map, ←assoc, colimit.ι_map, assoc, colimit.ι_pre] <;> rfl

theorem colimit.pre_map' [has_colimits_of_shape K C] (F : J ⥤ C) {E₁ E₂ : K ⥤ J} (α : E₁ ⟶ E₂) :
  colimit.pre F E₁ = colim.map (whisker_right α F) ≫ colimit.pre F E₂ :=
  by 
    ext1 <;> simp [←category.assoc]

theorem colimit.pre_id (F : J ⥤ C) : colimit.pre F (𝟭 _) = colim.map (functor.left_unitor F).Hom :=
  by 
    tidy

theorem colimit.map_post {D : Type u'} [category.{v} D] [has_colimits_of_shape J D] (H : C ⥤ D) :
  colimit.post F H ≫ H.map (colim.map α) = colim.map (whisker_right α H) ≫ colimit.post G H :=
  by 
    ext 
    rw [←assoc, colimit.ι_post, ←H.map_comp, colimit.ι_map, H.map_comp]
    rw [←assoc, colimit.ι_map, assoc, colimit.ι_post]
    rfl

/--
The isomorphism between
morphisms from the cone point of the colimit cocone for `F` to `W`
and cocones over `F` with cone point `W`
is natural in `F`.
-/
def colim_coyoneda : colim.op ⋙ coyoneda ≅ CategoryTheory.cocones J C :=
  nat_iso.of_components
    (fun F =>
      nat_iso.of_components (colimit.hom_iso (unop F))
        (by 
          tidy))
    (by 
      tidy)

end ColimFunctor

/--
We can transport colimits of shape `J` along an equivalence `J ≌ J'`.
-/
theorem has_colimits_of_shape_of_equivalence {J' : Type v} [small_category J'] (e : J ≌ J')
  [has_colimits_of_shape J C] : has_colimits_of_shape J' C :=
  by 
    constructor 
    intro F 
    apply has_colimit_of_equivalence_comp e 
    infer_instance

end Colimit

section Opposite

/--
If `t : cone F` is a limit cone, then `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit.op {t : cone F} (P : is_limit t) : is_colimit t.op :=
  { desc := fun s => (P.lift s.unop).op, fac' := fun s j => congr_argₓ Quiver.Hom.op (P.fac s.unop (unop j)),
    uniq' :=
      fun s m w =>
        by 
          rw [←P.uniq s.unop m.unop]
          ·
            rfl
          ·
            dsimp 
            intro j 
            rw [←w]
            rfl }

/--
If `t : cocone F` is a colimit cocone, then `t.op : cone F.op` is a limit cone.
-/
def is_colimit.op {t : cocone F} (P : is_colimit t) : is_limit t.op :=
  { lift := fun s => (P.desc s.unop).op, fac' := fun s j => congr_argₓ Quiver.Hom.op (P.fac s.unop (unop j)),
    uniq' :=
      fun s m w =>
        by 
          rw [←P.uniq s.unop m.unop]
          ·
            rfl
          ·
            dsimp 
            intro j 
            rw [←w]
            rfl }

/--
If `t : cone F.op` is a limit cone, then `t.unop : cocone F` is a colimit cocone.
-/
def is_limit.unop {t : cone F.op} (P : is_limit t) : is_colimit t.unop :=
  { desc := fun s => (P.lift s.op).unop, fac' := fun s j => congr_argₓ Quiver.Hom.unop (P.fac s.op (op j)),
    uniq' :=
      fun s m w =>
        by 
          rw [←P.uniq s.op m.op]
          ·
            rfl
          ·
            dsimp 
            intro j 
            rw [←w]
            rfl }

/--
If `t : cocone F.op` is a colimit cocone, then `t.unop : cone F.` is a limit cone.
-/
def is_colimit.unop {t : cocone F.op} (P : is_colimit t) : is_limit t.unop :=
  { lift := fun s => (P.desc s.op).unop, fac' := fun s j => congr_argₓ Quiver.Hom.unop (P.fac s.op (op j)),
    uniq' :=
      fun s m w =>
        by 
          rw [←P.uniq s.op m.op]
          ·
            rfl
          ·
            dsimp 
            intro j 
            rw [←w]
            rfl }

/--
`t : cone F` is a limit cone if and only is `t.op : cocone F.op` is a colimit cocone.
-/
def is_limit_equiv_is_colimit_op {t : cone F} : is_limit t ≃ is_colimit t.op :=
  equivOfSubsingletonOfSubsingleton is_limit.op
    fun P =>
      P.unop.of_iso_limit
        (cones.ext (iso.refl _)
          (by 
            tidy))

/--
`t : cocone F` is a colimit cocone if and only is `t.op : cone F.op` is a limit cone.
-/
def is_colimit_equiv_is_limit_op {t : cocone F} : is_colimit t ≃ is_limit t.op :=
  equivOfSubsingletonOfSubsingleton is_colimit.op
    fun P =>
      P.unop.of_iso_colimit
        (cocones.ext (iso.refl _)
          (by 
            tidy))

end Opposite

end CategoryTheory.Limits

