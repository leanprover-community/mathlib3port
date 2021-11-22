import Mathbin.AlgebraicGeometry.PresheafedSpace 
import Mathbin.Topology.Category.Top.Limits 
import Mathbin.Topology.Sheaves.Limits 
import Mathbin.CategoryTheory.Limits.ConcreteCategory

/-!
# `PresheafedSpace C` has colimits.

If `C` has limits, then the category `PresheafedSpace C` has colimits,
and the forgetful functor to `Top` preserves these colimits.

When restricted to a diagram where the underlying continuous maps are open embeddings,
this says that we can glue presheaved spaces.

Given a diagram `F : J ⥤ PresheafedSpace C`,
we first build the colimit of the underlying topological spaces,
as `colimit (F ⋙ PresheafedSpace.forget C)`. Call that colimit space `X`.

Our strategy is to push each of the presheaves `F.obj j`
forward along the continuous map `colimit.ι (F ⋙ PresheafedSpace.forget C) j` to `X`.
Since pushforward is functorial, we obtain a diagram `J ⥤ (presheaf C X)ᵒᵖ`
of presheaves on a single space `X`.
(Note that the arrows now point the other direction,
because this is the way `PresheafedSpace C` is set up.)

The limit of this diagram then constitutes the colimit presheaf.
-/


noncomputable theory

universe v u

open CategoryTheory

open Top

open Top.Presheaf

open TopologicalSpace

open Opposite

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Functor

variable{J : Type v}[small_category J]

variable{C : Type u}[category.{v} C]

namespace AlgebraicGeometry

namespace PresheafedSpace

@[simp]
theorem map_id_c_app (F : J ⥤ PresheafedSpace C) j U :
  (F.map (𝟙 j)).c.app (op U) =
    (pushforward.id (F.obj j).Presheaf).inv.app (op U) ≫
      (pushforward_eq
              (by 
                simp 
                rfl)
              (F.obj j).Presheaf).Hom.app
        (op U) :=
  by 
    cases U 
    dsimp 
    simp [PresheafedSpace.congr_app (F.map_id j)]
    rfl

@[simp]
theorem map_comp_c_app (F : J ⥤ PresheafedSpace C) {j₁ j₂ j₃} (f : j₁ ⟶ j₂) (g : j₂ ⟶ j₃) U :
  (F.map (f ≫ g)).c.app (op U) =
    (F.map g).c.app (op U) ≫
      (pushforward_map (F.map g).base (F.map f).c).app (op U) ≫
        (pushforward.comp (F.obj j₁).Presheaf (F.map f).base (F.map g).base).inv.app (op U) ≫
          (pushforward_eq
                  (by 
                    rw [F.map_comp]
                    rfl)
                  _).Hom.app
            _ :=
  by 
    cases U 
    dsimp 
    simp only [PresheafedSpace.congr_app (F.map_comp f g)]
    dsimp 
    simp 
    dsimp 
    simp 

/--
Given a diagram of presheafed spaces,
we can push all the presheaves forward to the colimit `X` of the underlying topological spaces,
obtaining a diagram in `(presheaf C X)ᵒᵖ`.
-/
@[simps]
def pushforward_diagram_to_colimit (F : J ⥤ PresheafedSpace C) :
  J ⥤ «expr ᵒᵖ» (presheaf C (colimit (F ⋙ PresheafedSpace.forget C))) :=
  { obj := fun j => op (colimit.ι (F ⋙ PresheafedSpace.forget C) j _* (F.obj j).Presheaf),
    map :=
      fun j j' f =>
        (pushforward_map (colimit.ι (F ⋙ PresheafedSpace.forget C) j') (F.map f).c ≫
            (pushforward.comp (F.obj j).Presheaf ((F ⋙ PresheafedSpace.forget C).map f)
                  (colimit.ι (F ⋙ PresheafedSpace.forget C) j')).inv ≫
              (pushforward_eq (colimit.w (F ⋙ PresheafedSpace.forget C) f) (F.obj j).Presheaf).Hom).op,
    map_id' :=
      fun j =>
        by 
          apply (op_equiv _ _).Injective 
          ext U 
          induction U using Opposite.rec 
          cases U 
          dsimp 
          simp 
          dsimp 
          simp ,
    map_comp' :=
      fun j₁ j₂ j₃ f g =>
        by 
          apply (op_equiv _ _).Injective 
          ext U 
          dsimp 
          simp only [map_comp_c_app, id.def, eq_to_hom_op, pushforward_map_app, eq_to_hom_map, assoc, id_comp,
            pushforward.comp_inv_app, pushforward_eq_hom_app]
          dsimp 
          simp only [eq_to_hom_trans, id_comp]
          congr 1
          rw [(F.map f).c.congr]
          swap 3
          refine' op ((opens.map (colimit.ι (F ⋙ PresheafedSpace.forget C) j₂)).obj (unop U))
          swap 2
          ·
            apply unop_injective 
            rw [←opens.map_comp_obj]
            congr 
            exact colimit.w (F ⋙ PresheafedSpace.forget C) g 
          swap 2
          ·
            simp 
            rfl }

variable[has_limits C]

/--
Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
@[simps]
def colimit (F : J ⥤ PresheafedSpace C) : PresheafedSpace C :=
  { Carrier := colimit (F ⋙ PresheafedSpace.forget C), Presheaf := limit (pushforward_diagram_to_colimit F).leftOp }

/--
Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
@[simps]
def colimit_cocone (F : J ⥤ PresheafedSpace C) : cocone F :=
  { x := colimit F,
    ι :=
      { app := fun j => { base := colimit.ι (F ⋙ PresheafedSpace.forget C) j, c := limit.π _ (op j) },
        naturality' :=
          fun j j' f =>
            by 
              fapply PresheafedSpace.ext
              ·
                ext x 
                exact colimit.w_apply (F ⋙ PresheafedSpace.forget C) f x
              ·
                ext U 
                induction U using Opposite.rec 
                cases U 
                dsimp 
                simp only [PresheafedSpace.id_c_app, eq_to_hom_op, eq_to_hom_map, assoc, pushforward.comp_inv_app]
                rw [←congr_argₓ nat_trans.app (limit.w (pushforward_diagram_to_colimit F).leftOp f.op)]
                dsimp 
                simp only [eq_to_hom_op, eq_to_hom_map, assoc, id_comp, pushforward.comp_inv_app]
                congr 
                dsimp 
                simp only [id_comp]
                simpa } }

namespace ColimitCoconeIsColimit

/--
Auxiliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def desc_c_app (F : J ⥤ PresheafedSpace C) (s : cocone F) (U : «expr ᵒᵖ» (opens («expr↥ » s.X.carrier))) :
  s.X.presheaf.obj U ⟶
    (colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s) _*
          limit (pushforward_diagram_to_colimit F).leftOp).obj
      U :=
  by 
    refine'
      limit.lift _ { x := s.X.presheaf.obj U, π := { app := fun j => _, naturality' := fun j j' f => _ } } ≫
        (limit_obj_iso_limit_comp_evaluation _ _).inv
    ·
      refine' (s.ι.app (unop j)).c.app U ≫ (F.obj (unop j)).Presheaf.map (eq_to_hom _)
      dsimp 
      rw [←opens.map_comp_obj]
      simp 
    ·
      rw [PresheafedSpace.congr_app (s.w f.unop).symm U]
      dsimp 
      have w :=
        functor.congr_obj (congr_argₓ opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
          (unop U)
      simp only [opens.map_comp_obj_unop] at w 
      replace w := congr_argₓ op w 
      have w' := nat_trans.congr (F.map f.unop).c w 
      rw [w']
      dsimp 
      simp 
      dsimp 
      simp 

theorem desc_c_naturality (F : J ⥤ PresheafedSpace C) (s : cocone F) {U V : «expr ᵒᵖ» (opens («expr↥ » s.X.carrier))}
  (i : U ⟶ V) :
  s.X.presheaf.map i ≫ desc_c_app F s V =
    desc_c_app F s U ≫ (colimit.desc (F ⋙ forget C) ((forget C).mapCocone s) _* (colimit_cocone F).x.Presheaf).map i :=
  by 
    dsimp [desc_c_app]
    ext 
    simp only [limit.lift_π, nat_trans.naturality, limit.lift_π_assoc, eq_to_hom_map, assoc, pushforward_obj_map,
      nat_trans.naturality_assoc, op_map, limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc,
      limit_obj_iso_limit_comp_evaluation_inv_π_app]
    dsimp 
    have w :=
      functor.congr_hom (congr_argₓ opens.map (colimit.ι_desc ((PresheafedSpace.forget C).mapCocone s) (unop j)))
        i.unop 
    simp only [opens.map_comp_map] at w 
    replace w := congr_argₓ Quiver.Hom.op w 
    rw [w]
    dsimp 
    simp 

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

/--
Auxiliary definition for `PresheafedSpace.has_colimits`.
-/
def colimit_cocone_is_colimit (F : J ⥤ PresheafedSpace C) : is_colimit (colimit_cocone F) :=
  { desc :=
      fun s =>
        { base := colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s),
          c := { app := fun U => desc_c_app F s U, naturality' := fun U V i => desc_c_naturality F s i } },
    fac' :=
      by 
        intro s j 
        dsimp 
        fapply PresheafedSpace.ext
        ·
          simp 
        ·
          ext 
          dsimp [desc_c_app]
          simp only [eq_to_hom_op, limit.lift_π_assoc, eq_to_hom_map, assoc, pushforward.comp_inv_app,
            limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc]
          dsimp 
          simp ,
    uniq' :=
      fun s m w =>
        by 
          have t : m.base = colimit.desc (F ⋙ PresheafedSpace.forget C) ((PresheafedSpace.forget C).mapCocone s)
          ·
            ext 
            dsimp 
            simp only [colimit.ι_desc_apply, map_cocone_ι_app]
            rw [←w j]
            simp 
          fapply PresheafedSpace.ext
          ·
            exact t
          ·
            ext U j 
            dsimp [desc_c_app]
            simp only [limit.lift_π, eq_to_hom_op, eq_to_hom_map, assoc, limit_obj_iso_limit_comp_evaluation_inv_π_app]
            rw [PresheafedSpace.congr_app (w (unop j)).symm U]
            dsimp 
            have w := congr_argₓ op (functor.congr_obj (congr_argₓ opens.map t) (unop U))
            rw [nat_trans.congr (limit.π (pushforward_diagram_to_colimit F).leftOp j) w]
            simpa }

/--
When `C` has limits, the category of presheaved spaces with values in `C` itself has colimits.
-/
instance  : has_colimits (PresheafedSpace C) :=
  { HasColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI
            { HasColimit :=
                fun F => has_colimit.mk { Cocone := colimit_cocone F, IsColimit := colimit_cocone_is_colimit F } } }

/--
The underlying topological space of a colimit of presheaved spaces is
the colimit of the underlying topological spaces.
-/
instance forget_preserves_colimits : preserves_colimits (PresheafedSpace.forget C) :=
  { PreservesColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exactI
            { PreservesColimit :=
                fun F =>
                  preserves_colimit_of_preserves_colimit_cocone (colimit_cocone_is_colimit F)
                    (by 
                      apply is_colimit.of_iso_colimit (colimit.is_colimit _)
                      fapply cocones.ext
                      ·
                        rfl
                      ·
                        intro j 
                        dsimp 
                        simp ) } }

end PresheafedSpace

end AlgebraicGeometry

