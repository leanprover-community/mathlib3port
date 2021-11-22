import Mathbin.CategoryTheory.Limits.HasLimits

/-!
# Preservation and reflection of (co)limits.

There are various distinct notions of "preserving limits". The one we
aim to capture here is: A functor F : C → D "preserves limits" if it
sends every limit cone in C to a limit cone in D. Informally, F
preserves all the limits which exist in C.

Note that:

* Of course, we do not want to require F to *strictly* take chosen
  limit cones of C to chosen limit cones of D. Indeed, the above
  definition makes no reference to a choice of limit cones so it makes
  sense without any conditions on C or D.

* Some diagrams in C may have no limit. In this case, there is no
  condition on the behavior of F on such diagrams. There are other
  notions (such as "flat functor") which impose conditions also on
  diagrams in C with no limits, but these are not considered here.

In order to be able to express the property of preserving limits of a
certain form, we say that a functor F preserves the limit of a
diagram K if F sends every limit cone on K to a limit cone. This is
vacuously satisfied when K does not admit a limit, which is consistent
with the above definition of "preserves limits".
-/


open CategoryTheory

noncomputable theory

namespace CategoryTheory.Limits

universe v u₁ u₂ u₃

variable{C : Type u₁}[category.{v} C]

variable{D : Type u₂}[category.{v} D]

variable{J : Type v}[small_category J]{K : J ⥤ C}

/--
A functor `F` preserves limits of `K` (written as `preserves_limit K F`)
if `F` maps any limit cone over `K` to a limit cone.
-/
class preserves_limit(K : J ⥤ C)(F : C ⥤ D) : Type max u₁ u₂ v where 
  preserves : ∀ {c : cone K}, is_limit c → is_limit (F.map_cone c)

/--
A functor `F` preserves colimits of `K` (written as `preserves_colimit K F`)
if `F` maps any colimit cocone over `K` to a colimit cocone.
-/
class preserves_colimit(K : J ⥤ C)(F : C ⥤ D) : Type max u₁ u₂ v where 
  preserves : ∀ {c : cocone K}, is_colimit c → is_colimit (F.map_cocone c)

/-- We say that `F` preserves limits of shape `J` if `F` preserves limits for every diagram
    `K : J ⥤ C`, i.e., `F` maps limit cones over `K` to limit cones. -/
class preserves_limits_of_shape(J : Type v)[small_category J](F : C ⥤ D) : Type max u₁ u₂ v where 
  PreservesLimit : ∀ {K : J ⥤ C}, preserves_limit K F :=  by 
  runTac 
    tactic.apply_instance

/-- We say that `F` preserves colimits of shape `J` if `F` preserves colimits for every diagram
    `K : J ⥤ C`, i.e., `F` maps colimit cocones over `K` to colimit cocones. -/
class preserves_colimits_of_shape(J : Type v)[small_category J](F : C ⥤ D) : Type max u₁ u₂ v where 
  PreservesColimit : ∀ {K : J ⥤ C}, preserves_colimit K F :=  by 
  runTac 
    tactic.apply_instance

/-- We say that `F` preserves limits if it sends limit cones over any diagram to limit cones. -/
class preserves_limits(F : C ⥤ D) : Type max u₁ u₂ (v + 1) where 
  PreservesLimitsOfShape : ∀ {J : Type v} [small_category J], preserves_limits_of_shape J F :=  by 
  runTac 
    tactic.apply_instance

/-- We say that `F` preserves colimits if it sends colimit cocones over any diagram to colimit
    cocones.-/
class preserves_colimits(F : C ⥤ D) : Type max u₁ u₂ (v + 1) where 
  PreservesColimitsOfShape : ∀ {J : Type v} [small_category J], preserves_colimits_of_shape J F :=  by 
  runTac 
    tactic.apply_instance

attribute [instance] preserves_limits_of_shape.preserves_limit preserves_limits.preserves_limits_of_shape
  preserves_colimits_of_shape.preserves_colimit preserves_colimits.preserves_colimits_of_shape

/--
A convenience function for `preserves_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_limit_of_preserves (F : C ⥤ D) {c : cone K} (t : is_limit c) [preserves_limit K F] : is_limit (F.map_cone c) :=
  preserves_limit.preserves t

/--
A convenience function for `preserves_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_colimit_of_preserves (F : C ⥤ D) {c : cocone K} (t : is_colimit c) [preserves_colimit K F] :
  is_colimit (F.map_cocone c) :=
  preserves_colimit.preserves t

instance preserves_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (preserves_limit K F) :=
  by 
    split  <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance preserves_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (preserves_colimit K F) :=
  by 
    split  <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance preserves_limits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  Subsingleton (preserves_limits_of_shape J F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    congr

instance preserves_colimits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  Subsingleton (preserves_colimits_of_shape J F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    congr

instance preserves_limits_subsingleton (F : C ⥤ D) : Subsingleton (preserves_limits F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    cc

instance preserves_colimits_subsingleton (F : C ⥤ D) : Subsingleton (preserves_colimits F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    cc

instance id_preserves_limits : preserves_limits (𝟭 C) :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        { PreservesLimit :=
            fun K =>
              by 
                exactI
                  ⟨fun c h =>
                      ⟨fun s => h.lift ⟨s.X, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩,
                        by 
                          cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j,
                        by 
                          cases K <;>
                            rcases c with ⟨_, _, _⟩ <;>
                              intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ } }

instance id_preserves_colimits : preserves_colimits (𝟭 C) :=
  { PreservesColimitsOfShape :=
      fun J 𝒥 =>
        { PreservesColimit :=
            fun K =>
              by 
                exactI
                  ⟨fun c h =>
                      ⟨fun s => h.desc ⟨s.X, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩,
                        by 
                          cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j,
                        by 
                          cases K <;>
                            rcases c with ⟨_, _, _⟩ <;>
                              intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ } }

section 

variable{E : Type u₃}[ℰ : category.{v} E]

variable(F : C ⥤ D)(G : D ⥤ E)

attribute [local elabWithoutExpectedType] preserves_limit.preserves preserves_colimit.preserves

instance comp_preserves_limit [preserves_limit K F] [preserves_limit (K ⋙ F) G] : preserves_limit K (F ⋙ G) :=
  ⟨fun c h => preserves_limit.preserves (preserves_limit.preserves h)⟩

instance comp_preserves_limits_of_shape [preserves_limits_of_shape J F] [preserves_limits_of_shape J G] :
  preserves_limits_of_shape J (F ⋙ G) :=
  {  }

instance comp_preserves_limits [preserves_limits F] [preserves_limits G] : preserves_limits (F ⋙ G) :=
  {  }

instance comp_preserves_colimit [preserves_colimit K F] [preserves_colimit (K ⋙ F) G] : preserves_colimit K (F ⋙ G) :=
  ⟨fun c h => preserves_colimit.preserves (preserves_colimit.preserves h)⟩

instance comp_preserves_colimits_of_shape [preserves_colimits_of_shape J F] [preserves_colimits_of_shape J G] :
  preserves_colimits_of_shape J (F ⋙ G) :=
  {  }

instance comp_preserves_colimits [preserves_colimits F] [preserves_colimits G] : preserves_colimits (F ⋙ G) :=
  {  }

end 

/-- If F preserves one limit cone for the diagram K,
  then it preserves any limit cone for K. -/
def preserves_limit_of_preserves_limit_cone {F : C ⥤ D} {t : cone K} (h : is_limit t) (hF : is_limit (F.map_cone t)) :
  preserves_limit K F :=
  ⟨fun t' h' => is_limit.of_iso_limit hF (functor.map_iso _ (is_limit.unique_up_to_iso h h'))⟩

/-- Transfer preservation of limits along a natural isomorphism in the diagram. -/
def preserves_limit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [preserves_limit K₁ F] :
  preserves_limit K₂ F :=
  { preserves :=
      fun c t =>
        by 
          apply is_limit.postcompose_inv_equiv (iso_whisker_right h F : _) _ _ 
          have  := (is_limit.postcompose_inv_equiv h c).symm t 
          apply is_limit.of_iso_limit (is_limit_of_preserves F this)
          refine'
            cones.ext (iso.refl _)
              fun j =>
                by 
                  tidy }

/-- Transfer preservation of a limit along a natural isomorphism in the functor. -/
def preserves_limit_of_nat_iso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [preserves_limit K F] : preserves_limit K G :=
  { preserves := fun c t => is_limit.map_cone_equiv h (preserves_limit.preserves t) }

/-- Transfer preservation of limits of shape along a natural isomorphism in the functor. -/
def preserves_limits_of_shape_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [preserves_limits_of_shape J F] :
  preserves_limits_of_shape J G :=
  { PreservesLimit := fun K => preserves_limit_of_nat_iso K h }

/-- Transfer preservation of limits along a natural isomorphism in the functor. -/
def preserves_limits_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [preserves_limits F] : preserves_limits G :=
  { PreservesLimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI preserves_limits_of_shape_of_nat_iso h }

/-- Transfer preservation of limits along a equivalence in the shape. -/
def preserves_limits_of_shape_of_equiv {J' : Type v} [small_category J'] (e : J ≌ J') (F : C ⥤ D)
  [preserves_limits_of_shape J F] : preserves_limits_of_shape J' F :=
  { PreservesLimit :=
      fun K =>
        { preserves :=
            fun c t =>
              by 
                let equ := e.inv_fun_id_assoc (K ⋙ F)
                have  := (is_limit_of_preserves F (t.whisker_equivalence e)).whiskerEquivalence e.symm 
                apply ((is_limit.postcompose_hom_equiv equ _).symm this).ofIsoLimit 
                refine' cones.ext (iso.refl _) fun j => _
                ·
                  dsimp 
                  simp [←functor.map_comp] } }

/-- If F preserves one colimit cocone for the diagram K,
  then it preserves any colimit cocone for K. -/
def preserves_colimit_of_preserves_colimit_cocone {F : C ⥤ D} {t : cocone K} (h : is_colimit t)
  (hF : is_colimit (F.map_cocone t)) : preserves_colimit K F :=
  ⟨fun t' h' => is_colimit.of_iso_colimit hF (functor.map_iso _ (is_colimit.unique_up_to_iso h h'))⟩

/-- Transfer preservation of colimits along a natural isomorphism in the shape. -/
def preserves_colimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [preserves_colimit K₁ F] :
  preserves_colimit K₂ F :=
  { preserves :=
      fun c t =>
        by 
          apply is_colimit.precompose_hom_equiv (iso_whisker_right h F : _) _ _ 
          have  := (is_colimit.precompose_hom_equiv h c).symm t 
          apply is_colimit.of_iso_colimit (is_colimit_of_preserves F this)
          refine'
            cocones.ext (iso.refl _)
              fun j =>
                by 
                  tidy }

/-- Transfer preservation of a colimit along a natural isomorphism in the functor. -/
def preserves_colimit_of_nat_iso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [preserves_colimit K F] :
  preserves_colimit K G :=
  { preserves := fun c t => is_colimit.map_cocone_equiv h (preserves_colimit.preserves t) }

/-- Transfer preservation of colimits of shape along a natural isomorphism in the functor. -/
def preserves_colimits_of_shape_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [preserves_colimits_of_shape J F] :
  preserves_colimits_of_shape J G :=
  { PreservesColimit := fun K => preserves_colimit_of_nat_iso K h }

/-- Transfer preservation of colimits along a natural isomorphism in the functor. -/
def preserves_colimits_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [preserves_colimits F] : preserves_colimits G :=
  { PreservesColimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI preserves_colimits_of_shape_of_nat_iso h }

/-- Transfer preservation of colimits along a equivalence in the shape. -/
def preserves_colimits_of_shape_of_equiv {J' : Type v} [small_category J'] (e : J ≌ J') (F : C ⥤ D)
  [preserves_colimits_of_shape J F] : preserves_colimits_of_shape J' F :=
  { PreservesColimit :=
      fun K =>
        { preserves :=
            fun c t =>
              by 
                let equ := e.inv_fun_id_assoc (K ⋙ F)
                have  := (is_colimit_of_preserves F (t.whisker_equivalence e)).whiskerEquivalence e.symm 
                apply ((is_colimit.precompose_inv_equiv equ _).symm this).ofIsoColimit 
                refine' cocones.ext (iso.refl _) fun j => _
                ·
                  dsimp 
                  simp [←functor.map_comp] } }

/--
A functor `F : C ⥤ D` reflects limits for `K : J ⥤ C` if
whenever the image of a cone over `K` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class reflects_limit(K : J ⥤ C)(F : C ⥤ D) : Type max u₁ u₂ v where 
  reflects : ∀ {c : cone K}, is_limit (F.map_cone c) → is_limit c

/--
A functor `F : C ⥤ D` reflects colimits for `K : J ⥤ C` if
whenever the image of a cocone over `K` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class reflects_colimit(K : J ⥤ C)(F : C ⥤ D) : Type max u₁ u₂ v where 
  reflects : ∀ {c : cocone K}, is_colimit (F.map_cocone c) → is_colimit c

/--
A functor `F : C ⥤ D` reflects limits of shape `J` if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class reflects_limits_of_shape(J : Type v)[small_category J](F : C ⥤ D) : Type max u₁ u₂ v where 
  ReflectsLimit : ∀ {K : J ⥤ C}, reflects_limit K F :=  by 
  runTac 
    tactic.apply_instance

/--
A functor `F : C ⥤ D` reflects colimits of shape `J` if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class reflects_colimits_of_shape(J : Type v)[small_category J](F : C ⥤ D) : Type max u₁ u₂ v where 
  ReflectsColimit : ∀ {K : J ⥤ C}, reflects_colimit K F :=  by 
  runTac 
    tactic.apply_instance

/--
A functor `F : C ⥤ D` reflects limits if
whenever the image of a cone over some `K : J ⥤ C` under `F` is a limit cone in `D`,
the cone was already a limit cone in `C`.
Note that we do not assume a priori that `D` actually has any limits.
-/
class reflects_limits(F : C ⥤ D) : Type max u₁ u₂ (v + 1) where 
  ReflectsLimitsOfShape : ∀ {J : Type v} [small_category J], reflects_limits_of_shape J F :=  by 
  runTac 
    tactic.apply_instance

/--
A functor `F : C ⥤ D` reflects colimits if
whenever the image of a cocone over some `K : J ⥤ C` under `F` is a colimit cocone in `D`,
the cocone was already a colimit cocone in `C`.
Note that we do not assume a priori that `D` actually has any colimits.
-/
class reflects_colimits(F : C ⥤ D) : Type max u₁ u₂ (v + 1) where 
  ReflectsColimitsOfShape : ∀ {J : Type v} [small_category J], reflects_colimits_of_shape J F :=  by 
  runTac 
    tactic.apply_instance

/--
A convenience function for `reflects_limit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_limit_of_reflects (F : C ⥤ D) {c : cone K} (t : is_limit (F.map_cone c)) [reflects_limit K F] : is_limit c :=
  reflects_limit.reflects t

/--
A convenience function for `reflects_colimit`, which takes the functor as an explicit argument to
guide typeclass resolution.
-/
def is_colimit_of_reflects (F : C ⥤ D) {c : cocone K} (t : is_colimit (F.map_cocone c)) [reflects_colimit K F] :
  is_colimit c :=
  reflects_colimit.reflects t

instance reflects_limit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (reflects_limit K F) :=
  by 
    split  <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance reflects_colimit_subsingleton (K : J ⥤ C) (F : C ⥤ D) : Subsingleton (reflects_colimit K F) :=
  by 
    split  <;> rintro ⟨a⟩ ⟨b⟩ <;> congr

instance reflects_limits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  Subsingleton (reflects_limits_of_shape J F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    congr

instance reflects_colimits_of_shape_subsingleton (J : Type v) [small_category J] (F : C ⥤ D) :
  Subsingleton (reflects_colimits_of_shape J F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    congr

instance reflects_limits_subsingleton (F : C ⥤ D) : Subsingleton (reflects_limits F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    cc

instance reflects_colimits_subsingleton (F : C ⥤ D) : Subsingleton (reflects_colimits F) :=
  by 
    split 
    intros 
    cases a 
    cases b 
    cc

instance (priority := 100)reflects_limit_of_reflects_limits_of_shape (K : J ⥤ C) (F : C ⥤ D)
  [H : reflects_limits_of_shape J F] : reflects_limit K F :=
  reflects_limits_of_shape.reflects_limit

instance (priority := 100)reflects_colimit_of_reflects_colimits_of_shape (K : J ⥤ C) (F : C ⥤ D)
  [H : reflects_colimits_of_shape J F] : reflects_colimit K F :=
  reflects_colimits_of_shape.reflects_colimit

instance (priority := 100)reflects_limits_of_shape_of_reflects_limits (F : C ⥤ D) [H : reflects_limits F] :
  reflects_limits_of_shape J F :=
  reflects_limits.reflects_limits_of_shape

instance (priority := 100)reflects_colimits_of_shape_of_reflects_colimits (F : C ⥤ D) [H : reflects_colimits F] :
  reflects_colimits_of_shape J F :=
  reflects_colimits.reflects_colimits_of_shape

instance id_reflects_limits : reflects_limits (𝟭 C) :=
  { ReflectsLimitsOfShape :=
      fun J 𝒥 =>
        { ReflectsLimit :=
            fun K =>
              by 
                exactI
                  ⟨fun c h =>
                      ⟨fun s => h.lift ⟨s.X, fun j => s.π.app j, fun j j' f => s.π.naturality f⟩,
                        by 
                          cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j,
                        by 
                          cases K <;>
                            rcases c with ⟨_, _, _⟩ <;>
                              intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ } }

instance id_reflects_colimits : reflects_colimits (𝟭 C) :=
  { ReflectsColimitsOfShape :=
      fun J 𝒥 =>
        { ReflectsColimit :=
            fun K =>
              by 
                exactI
                  ⟨fun c h =>
                      ⟨fun s => h.desc ⟨s.X, fun j => s.ι.app j, fun j j' f => s.ι.naturality f⟩,
                        by 
                          cases K <;> rcases c with ⟨_, _, _⟩ <;> intro s j <;> cases s <;> exact h.fac _ j,
                        by 
                          cases K <;>
                            rcases c with ⟨_, _, _⟩ <;>
                              intro s m w <;> rcases s with ⟨_, _, _⟩ <;> exact h.uniq _ m w⟩⟩ } }

section 

variable{E : Type u₃}[ℰ : category.{v} E]

variable(F : C ⥤ D)(G : D ⥤ E)

instance comp_reflects_limit [reflects_limit K F] [reflects_limit (K ⋙ F) G] : reflects_limit K (F ⋙ G) :=
  ⟨fun c h => reflects_limit.reflects (reflects_limit.reflects h)⟩

instance comp_reflects_limits_of_shape [reflects_limits_of_shape J F] [reflects_limits_of_shape J G] :
  reflects_limits_of_shape J (F ⋙ G) :=
  {  }

instance comp_reflects_limits [reflects_limits F] [reflects_limits G] : reflects_limits (F ⋙ G) :=
  {  }

instance comp_reflects_colimit [reflects_colimit K F] [reflects_colimit (K ⋙ F) G] : reflects_colimit K (F ⋙ G) :=
  ⟨fun c h => reflects_colimit.reflects (reflects_colimit.reflects h)⟩

instance comp_reflects_colimits_of_shape [reflects_colimits_of_shape J F] [reflects_colimits_of_shape J G] :
  reflects_colimits_of_shape J (F ⋙ G) :=
  {  }

instance comp_reflects_colimits [reflects_colimits F] [reflects_colimits G] : reflects_colimits (F ⋙ G) :=
  {  }

/-- If `F ⋙ G` preserves limits for `K`, and `G` reflects limits for `K ⋙ F`,
then `F` preserves limits for `K`. -/
def preserves_limit_of_reflects_of_preserves [preserves_limit K (F ⋙ G)] [reflects_limit (K ⋙ F) G] :
  preserves_limit K F :=
  ⟨fun c h =>
      by 
        apply is_limit_of_reflects G 
        apply is_limit_of_preserves (F ⋙ G) h⟩

/--
If `F ⋙ G` preserves limits of shape `J` and `G` reflects limits of shape `J`, then `F` preserves
limits of shape `J`.
-/
def preserves_limits_of_shape_of_reflects_of_preserves [preserves_limits_of_shape J (F ⋙ G)]
  [reflects_limits_of_shape J G] : preserves_limits_of_shape J F :=
  { PreservesLimit := fun K => preserves_limit_of_reflects_of_preserves F G }

/-- If `F ⋙ G` preserves limits and `G` reflects limits, then `F` preserves limits. -/
def preserves_limits_of_reflects_of_preserves [preserves_limits (F ⋙ G)] [reflects_limits G] : preserves_limits F :=
  { PreservesLimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI preserves_limits_of_shape_of_reflects_of_preserves F G }

/-- Transfer reflection of limits along a natural isomorphism in the diagram. -/
def reflects_limit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [reflects_limit K₁ F] :
  reflects_limit K₂ F :=
  { reflects :=
      fun c t =>
        by 
          apply is_limit.postcompose_inv_equiv h c (is_limit_of_reflects F _)
          apply ((is_limit.postcompose_inv_equiv (iso_whisker_right h F : _) _).symm t).ofIsoLimit _ 
          exact
            cones.ext (iso.refl _)
              (by 
                tidy) }

/-- Transfer reflection of a limit along a natural isomorphism in the functor. -/
def reflects_limit_of_nat_iso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [reflects_limit K F] : reflects_limit K G :=
  { reflects := fun c t => reflects_limit.reflects (is_limit.map_cone_equiv h.symm t) }

/-- Transfer reflection of limits of shape along a natural isomorphism in the functor. -/
def reflects_limits_of_shape_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [reflects_limits_of_shape J F] :
  reflects_limits_of_shape J G :=
  { ReflectsLimit := fun K => reflects_limit_of_nat_iso K h }

/-- Transfer reflection of limits along a natural isomorphism in the functor. -/
def reflects_limits_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [reflects_limits F] : reflects_limits G :=
  { ReflectsLimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI reflects_limits_of_shape_of_nat_iso h }

/--
If the limit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the limit of `F`.
-/
def reflects_limit_of_reflects_isomorphisms (F : J ⥤ C) (G : C ⥤ D) [reflects_isomorphisms G] [has_limit F]
  [preserves_limit F G] : reflects_limit F G :=
  { reflects :=
      fun c t =>
        by 
          apply is_limit.of_point_iso (limit.is_limit F)
          change is_iso ((cones.forget _).map ((limit.is_limit F).liftConeMorphism c))
          apply (cones.forget F).map_is_iso _ 
          apply is_iso_of_reflects_iso _ (cones.functoriality F G)
          refine' t.hom_is_iso (is_limit_of_preserves G (limit.is_limit F)) _ }

/--
If `C` has limits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects limits of shape `J`.
-/
def reflects_limits_of_shape_of_reflects_isomorphisms {G : C ⥤ D} [reflects_isomorphisms G] [has_limits_of_shape J C]
  [preserves_limits_of_shape J G] : reflects_limits_of_shape J G :=
  { ReflectsLimit := fun F => reflects_limit_of_reflects_isomorphisms F G }

/--
If `C` has limits and `G` preserves limits, then if `G` reflects isomorphisms then it reflects
limits.
-/
def reflects_limits_of_reflects_isomorphisms {G : C ⥤ D} [reflects_isomorphisms G] [has_limits C] [preserves_limits G] :
  reflects_limits G :=
  { ReflectsLimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI reflects_limits_of_shape_of_reflects_isomorphisms }

/-- If `F ⋙ G` preserves colimits for `K`, and `G` reflects colimits for `K ⋙ F`,
then `F` preserves colimits for `K`. -/
def preserves_colimit_of_reflects_of_preserves [preserves_colimit K (F ⋙ G)] [reflects_colimit (K ⋙ F) G] :
  preserves_colimit K F :=
  ⟨fun c h =>
      by 
        apply is_colimit_of_reflects G 
        apply is_colimit_of_preserves (F ⋙ G) h⟩

/--
If `F ⋙ G` preserves colimits of shape `J` and `G` reflects colimits of shape `J`, then `F`
preserves colimits of shape `J`.
-/
def preserves_colimits_of_shape_of_reflects_of_preserves [preserves_colimits_of_shape J (F ⋙ G)]
  [reflects_colimits_of_shape J G] : preserves_colimits_of_shape J F :=
  { PreservesColimit := fun K => preserves_colimit_of_reflects_of_preserves F G }

/-- If `F ⋙ G` preserves colimits and `G` reflects colimits, then `F` preserves colimits. -/
def preserves_colimits_of_reflects_of_preserves [preserves_colimits (F ⋙ G)] [reflects_colimits G] :
  preserves_colimits F :=
  { PreservesColimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI preserves_colimits_of_shape_of_reflects_of_preserves F G }

/-- Transfer reflection of colimits along a natural isomorphism in the diagram. -/
def reflects_colimit_of_iso_diagram {K₁ K₂ : J ⥤ C} (F : C ⥤ D) (h : K₁ ≅ K₂) [reflects_colimit K₁ F] :
  reflects_colimit K₂ F :=
  { reflects :=
      fun c t =>
        by 
          apply is_colimit.precompose_hom_equiv h c (is_colimit_of_reflects F _)
          apply ((is_colimit.precompose_hom_equiv (iso_whisker_right h F : _) _).symm t).ofIsoColimit _ 
          exact
            cocones.ext (iso.refl _)
              (by 
                tidy) }

/-- Transfer reflection of a colimit along a natural isomorphism in the functor. -/
def reflects_colimit_of_nat_iso (K : J ⥤ C) {F G : C ⥤ D} (h : F ≅ G) [reflects_colimit K F] : reflects_colimit K G :=
  { reflects := fun c t => reflects_colimit.reflects (is_colimit.map_cocone_equiv h.symm t) }

/-- Transfer reflection of colimits of shape along a natural isomorphism in the functor. -/
def reflects_colimits_of_shape_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [reflects_colimits_of_shape J F] :
  reflects_colimits_of_shape J G :=
  { ReflectsColimit := fun K => reflects_colimit_of_nat_iso K h }

/-- Transfer reflection of colimits along a natural isomorphism in the functor. -/
def reflects_colimits_of_nat_iso {F G : C ⥤ D} (h : F ≅ G) [reflects_colimits F] : reflects_colimits G :=
  { ReflectsColimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI reflects_colimits_of_shape_of_nat_iso h }

/--
If the colimit of `F` exists and `G` preserves it, then if `G` reflects isomorphisms then it
reflects the colimit of `F`.
-/
def reflects_colimit_of_reflects_isomorphisms (F : J ⥤ C) (G : C ⥤ D) [reflects_isomorphisms G] [has_colimit F]
  [preserves_colimit F G] : reflects_colimit F G :=
  { reflects :=
      fun c t =>
        by 
          apply is_colimit.of_point_iso (colimit.is_colimit F)
          change is_iso ((cocones.forget _).map ((colimit.is_colimit F).descCoconeMorphism c))
          apply (cocones.forget F).map_is_iso _ 
          apply is_iso_of_reflects_iso _ (cocones.functoriality F G)
          refine' (is_colimit_of_preserves G (colimit.is_colimit F)).hom_is_iso t _ }

/--
If `C` has colimits of shape `J` and `G` preserves them, then if `G` reflects isomorphisms then it
reflects colimits of shape `J`.
-/
def reflects_colimits_of_shape_of_reflects_isomorphisms {G : C ⥤ D} [reflects_isomorphisms G]
  [has_colimits_of_shape J C] [preserves_colimits_of_shape J G] : reflects_colimits_of_shape J G :=
  { ReflectsColimit := fun F => reflects_colimit_of_reflects_isomorphisms F G }

/--
If `C` has colimits and `G` preserves colimits, then if `G` reflects isomorphisms then it reflects
colimits.
-/
def reflects_colimits_of_reflects_isomorphisms {G : C ⥤ D} [reflects_isomorphisms G] [has_colimits C]
  [preserves_colimits G] : reflects_colimits G :=
  { ReflectsColimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI reflects_colimits_of_shape_of_reflects_isomorphisms }

end 

variable(F : C ⥤ D)

/-- A fully faithful functor reflects limits. -/
def fully_faithful_reflects_limits [full F] [faithful F] : reflects_limits F :=
  { ReflectsLimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI
            { ReflectsLimit :=
                fun K =>
                  { reflects :=
                      fun c t =>
                        (is_limit.mk_cone_morphism
                            fun s => (cones.functoriality K F).Preimage (t.lift_cone_morphism _))$
                          by 
                            apply fun s m => (cones.functoriality K F).map_injective _ 
                            rw [functor.image_preimage]
                            apply t.uniq_cone_morphism } } }

/-- A fully faithful functor reflects colimits. -/
def fully_faithful_reflects_colimits [full F] [faithful F] : reflects_colimits F :=
  { ReflectsColimitsOfShape :=
      fun J 𝒥₁ =>
        by 
          exactI
            { ReflectsColimit :=
                fun K =>
                  { reflects :=
                      fun c t =>
                        (is_colimit.mk_cocone_morphism
                            fun s => (cocones.functoriality K F).Preimage (t.desc_cocone_morphism _))$
                          by 
                            apply fun s m => (cocones.functoriality K F).map_injective _ 
                            rw [functor.image_preimage]
                            apply t.uniq_cocone_morphism } } }

end CategoryTheory.Limits

