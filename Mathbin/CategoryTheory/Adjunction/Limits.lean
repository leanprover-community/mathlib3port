import Mathbin.CategoryTheory.Adjunction.Basic 
import Mathbin.CategoryTheory.Limits.Creates

/-!
# Adjunctions and limits

A left adjoint preserves colimits (`category_theory.adjunction.left_adjoint_preserves_colimits`),
and a right adjoint preserves limits (`category_theory.adjunction.right_adjoint_preserves_limits`).

Equivalences create and reflect (co)limits.
(`category_theory.adjunction.is_equivalence_creates_limits`,
`category_theory.adjunction.is_equivalence_creates_colimits`,
`category_theory.adjunction.is_equivalence_reflects_limits`,
`category_theory.adjunction.is_equivalence_reflects_colimits`,)

In `category_theory.adjunction.cocones_iso` we show that
when `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/


open Opposite

namespace CategoryTheory.Adjunction

open CategoryTheory

open CategoryTheory.Functor

open CategoryTheory.Limits

universe u₁ u₂ v

variable {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]

variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

include adj

section PreservationColimits

variable {J : Type v} [small_category J] (K : J ⥤ C)

/--
The right adjoint of `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
def functoriality_right_adjoint : cocone (K ⋙ F) ⥤ cocone K :=
  cocones.functoriality _ G ⋙ cocones.precompose (K.right_unitor.inv ≫ whisker_left K adj.unit ≫ (associator _ _ _).inv)

attribute [local reducible] functoriality_right_adjoint

/--
The unit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps]
def functoriality_unit : 𝟭 (cocone K) ⟶ cocones.functoriality _ F ⋙ functoriality_right_adjoint adj K :=
  { app := fun c => { Hom := adj.unit.app c.X } }

/--
The counit for the adjunction for `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)`.

Auxiliary definition for `functoriality_is_left_adjoint`.
-/
@[simps]
def functoriality_counit : functoriality_right_adjoint adj K ⋙ cocones.functoriality _ F ⟶ 𝟭 (cocone (K ⋙ F)) :=
  { app := fun c => { Hom := adj.counit.app c.X } }

/-- The functor `cocones.functoriality K F : cocone K ⥤ cocone (K ⋙ F)` is a left adjoint. -/
def functoriality_is_left_adjoint : is_left_adjoint (cocones.functoriality K F) :=
  { right := functoriality_right_adjoint adj K,
    adj := mk_of_unit_counit { Unit := functoriality_unit adj K, counit := functoriality_counit adj K } }

/--
A left adjoint preserves colimits.

See https://stacks.math.columbia.edu/tag/0038.
-/
def left_adjoint_preserves_colimits : preserves_colimits F :=
  { PreservesColimitsOfShape :=
      fun J 𝒥 =>
        { PreservesColimit :=
            fun F =>
              by 
                exact
                  { preserves :=
                      fun c hc =>
                        is_colimit.iso_unique_cocone_morphism.inv
                          fun s =>
                            @Equiv.unique _ _ (is_colimit.iso_unique_cocone_morphism.hom hc _)
                              ((adj.functoriality_is_left_adjoint _).adj.homEquiv _ _) } } }

omit adj

instance (priority := 100) is_equivalence_preserves_colimits (E : C ⥤ D) [is_equivalence E] : preserves_colimits E :=
  left_adjoint_preserves_colimits E.adjunction

-- error in CategoryTheory.Adjunction.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100]
instance is_equivalence_reflects_colimits (E : «expr ⥤ »(D, C)) [is_equivalence E] : reflects_colimits E :=
{ reflects_colimits_of_shape := λ
  J
  𝒥, by exactI [expr { reflects_colimit := λ
     K, { reflects := λ c t, begin
         have [ident l] [] [":=", expr (is_colimit_of_preserves E.inv t).map_cocone_equiv E.as_equivalence.unit_iso.symm],
         refine [expr ((is_colimit.precompose_inv_equiv K.right_unitor _).symm l).of_iso_colimit _],
         tidy []
       end } }] }

instance (priority := 100) is_equivalence_creates_colimits (H : D ⥤ C) [is_equivalence H] : creates_colimits H :=
  { CreatesColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { CreatesColimit :=
                fun F =>
                  { lifts :=
                      fun c t =>
                        { liftedCocone := H.map_cocone_inv c, validLift := H.map_cocone_map_cocone_inv c } } } }

example (E : C ⥤ D) [is_equivalence E] (c : cocone K) (h : is_colimit c) : is_colimit (E.map_cocone c) :=
  preserves_colimit.preserves h

theorem has_colimit_comp_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimit K] : has_colimit (K ⋙ E) :=
  has_colimit.mk
    { Cocone := E.map_cocone (colimit.cocone K), IsColimit := preserves_colimit.preserves (colimit.is_colimit K) }

theorem has_colimit_of_comp_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimit (K ⋙ E)] : has_colimit K :=
  @has_colimit_of_iso _ _ _ _ (K ⋙ E ⋙ inv E) K (@has_colimit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
    ((functor.right_unitor _).symm ≪≫ iso_whisker_left K E.as_equivalence.unit_iso)

/-- Transport a `has_colimits_of_shape` instance across an equivalence. -/
theorem has_colimits_of_shape_of_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimits_of_shape J D] :
  has_colimits_of_shape J C :=
  ⟨fun F =>
      by 
        exact has_colimit_of_comp_equivalence F E⟩

/-- Transport a `has_colimits` instance across an equivalence. -/
theorem has_colimits_of_equivalence (E : C ⥤ D) [is_equivalence E] [has_colimits D] : has_colimits C :=
  ⟨fun J hJ =>
      by 
        exact has_colimits_of_shape_of_equivalence E⟩

end PreservationColimits

section PreservationLimits

variable {J : Type v} [small_category J] (K : J ⥤ D)

/--
The left adjoint of `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
def functoriality_left_adjoint : cone (K ⋙ G) ⥤ cone K :=
  cones.functoriality _ F ⋙ cones.postcompose ((associator _ _ _).Hom ≫ whisker_left K adj.counit ≫ K.right_unitor.hom)

attribute [local reducible] functoriality_left_adjoint

/--
The unit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps]
def functoriality_unit' : 𝟭 (cone (K ⋙ G)) ⟶ functoriality_left_adjoint adj K ⋙ cones.functoriality _ G :=
  { app := fun c => { Hom := adj.unit.app c.X } }

/--
The counit for the adjunction for`cones.functoriality K G : cone K ⥤ cone (K ⋙ G)`.

Auxiliary definition for `functoriality_is_right_adjoint`.
-/
@[simps]
def functoriality_counit' : cones.functoriality _ G ⋙ functoriality_left_adjoint adj K ⟶ 𝟭 (cone K) :=
  { app := fun c => { Hom := adj.counit.app c.X } }

/-- The functor `cones.functoriality K G : cone K ⥤ cone (K ⋙ G)` is a right adjoint. -/
def functoriality_is_right_adjoint : is_right_adjoint (cones.functoriality K G) :=
  { left := functoriality_left_adjoint adj K,
    adj := mk_of_unit_counit { Unit := functoriality_unit' adj K, counit := functoriality_counit' adj K } }

/--
A right adjoint preserves limits.

See https://stacks.math.columbia.edu/tag/0038.
-/
def right_adjoint_preserves_limits : preserves_limits G :=
  { PreservesLimitsOfShape :=
      fun J 𝒥 =>
        { PreservesLimit :=
            fun K =>
              by 
                exact
                  { preserves :=
                      fun c hc =>
                        is_limit.iso_unique_cone_morphism.inv
                          fun s =>
                            @Equiv.unique _ _ (is_limit.iso_unique_cone_morphism.hom hc _)
                              ((adj.functoriality_is_right_adjoint _).adj.homEquiv _ _).symm } } }

omit adj

instance (priority := 100) is_equivalence_preserves_limits (E : D ⥤ C) [is_equivalence E] : preserves_limits E :=
  right_adjoint_preserves_limits E.inv.adjunction

-- error in CategoryTheory.Adjunction.Limits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
@[priority 100] instance is_equivalence_reflects_limits (E : «expr ⥤ »(D, C)) [is_equivalence E] : reflects_limits E :=
{ reflects_limits_of_shape := λ
  J
  𝒥, by exactI [expr { reflects_limit := λ
     K, { reflects := λ c t, begin
         have [] [] [":=", expr (is_limit_of_preserves E.inv t).map_cone_equiv E.as_equivalence.unit_iso.symm],
         refine [expr ((is_limit.postcompose_hom_equiv K.left_unitor _).symm this).of_iso_limit _],
         tidy []
       end } }] }

instance (priority := 100) is_equivalence_creates_limits (H : D ⥤ C) [is_equivalence H] : creates_limits H :=
  { CreatesLimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
            { CreatesLimit :=
                fun F =>
                  { lifts := fun c t => { liftedCone := H.map_cone_inv c, validLift := H.map_cone_map_cone_inv c } } } }

example (E : D ⥤ C) [is_equivalence E] (c : cone K) [h : is_limit c] : is_limit (E.map_cone c) :=
  preserves_limit.preserves h

theorem has_limit_comp_equivalence (E : D ⥤ C) [is_equivalence E] [has_limit K] : has_limit (K ⋙ E) :=
  has_limit.mk { Cone := E.map_cone (limit.cone K), IsLimit := preserves_limit.preserves (limit.is_limit K) }

theorem has_limit_of_comp_equivalence (E : D ⥤ C) [is_equivalence E] [has_limit (K ⋙ E)] : has_limit K :=
  @has_limit_of_iso _ _ _ _ (K ⋙ E ⋙ inv E) K (@has_limit_comp_equivalence _ _ _ _ _ _ (K ⋙ E) (inv E) _ _)
    (iso_whisker_left K E.as_equivalence.unit_iso.symm ≪≫ functor.right_unitor _)

/-- Transport a `has_limits_of_shape` instance across an equivalence. -/
theorem has_limits_of_shape_of_equivalence (E : D ⥤ C) [is_equivalence E] [has_limits_of_shape J C] :
  has_limits_of_shape J D :=
  ⟨fun F =>
      by 
        exact has_limit_of_comp_equivalence F E⟩

/-- Transport a `has_limits` instance across an equivalence. -/
theorem has_limits_of_equivalence (E : D ⥤ C) [is_equivalence E] [has_limits C] : has_limits D :=
  ⟨fun J hJ =>
      by 
        exact has_limits_of_shape_of_equivalence E⟩

end PreservationLimits

/-- auxiliary construction for `cocones_iso` -/
@[simps]
def cocones_iso_component_hom {J : Type v} [small_category J] {K : J ⥤ C} (Y : D)
  (t : ((cocones J D).obj (op (K ⋙ F))).obj Y) : (G ⋙ (cocones J C).obj (op K)).obj Y :=
  { app := fun j => (adj.hom_equiv (K.obj j) Y) (t.app j),
    naturality' :=
      fun j j' f =>
        by 
          erw [←adj.hom_equiv_naturality_left, t.naturality]
          dsimp 
          simp  }

/-- auxiliary construction for `cocones_iso` -/
@[simps]
def cocones_iso_component_inv {J : Type v} [small_category J] {K : J ⥤ C} (Y : D)
  (t : (G ⋙ (cocones J C).obj (op K)).obj Y) : ((cocones J D).obj (op (K ⋙ F))).obj Y :=
  { app := fun j => (adj.hom_equiv (K.obj j) Y).symm (t.app j),
    naturality' :=
      fun j j' f =>
        by 
          erw [←adj.hom_equiv_naturality_left_symm, ←adj.hom_equiv_naturality_right_symm, t.naturality]
          dsimp 
          simp  }

/--
When `F ⊣ G`,
the functor associating to each `Y` the cocones over `K ⋙ F` with cone point `Y`
is naturally isomorphic to
the functor associating to each `Y` the cocones over `K` with cone point `G.obj Y`.
-/
def cocones_iso {J : Type v} [small_category J] {K : J ⥤ C} :
  (cocones J D).obj (op (K ⋙ F)) ≅ G ⋙ (cocones J C).obj (op K) :=
  nat_iso.of_components (fun Y => { Hom := cocones_iso_component_hom adj Y, inv := cocones_iso_component_inv adj Y })
    (by 
      tidy)

/-- auxiliary construction for `cones_iso` -/
@[simps]
def cones_iso_component_hom {J : Type v} [small_category J] {K : J ⥤ D} (X : «expr ᵒᵖ» C)
  (t : (functor.op F ⋙ (cones J D).obj K).obj X) : ((cones J C).obj (K ⋙ G)).obj X :=
  { app := fun j => (adj.hom_equiv (unop X) (K.obj j)) (t.app j),
    naturality' :=
      fun j j' f =>
        by 
          erw [←adj.hom_equiv_naturality_right, ←t.naturality, category.id_comp, category.id_comp]
          rfl }

/-- auxiliary construction for `cones_iso` -/
@[simps]
def cones_iso_component_inv {J : Type v} [small_category J] {K : J ⥤ D} (X : «expr ᵒᵖ» C)
  (t : ((cones J C).obj (K ⋙ G)).obj X) : (functor.op F ⋙ (cones J D).obj K).obj X :=
  { app := fun j => (adj.hom_equiv (unop X) (K.obj j)).symm (t.app j),
    naturality' :=
      fun j j' f =>
        by 
          erw [←adj.hom_equiv_naturality_right_symm, ←t.naturality, category.id_comp, category.id_comp] }

/--
When `F ⊣ G`,
the functor associating to each `X` the cones over `K` with cone point `F.op.obj X`
is naturally isomorphic to
the functor associating to each `X` the cones over `K ⋙ G` with cone point `X`.
-/
def cones_iso {J : Type v} [small_category J] {K : J ⥤ D} : F.op ⋙ (cones J D).obj K ≅ (cones J C).obj (K ⋙ G) :=
  nat_iso.of_components (fun X => { Hom := cones_iso_component_hom adj X, inv := cones_iso_component_inv adj X })
    (by 
      tidy)

end CategoryTheory.Adjunction

