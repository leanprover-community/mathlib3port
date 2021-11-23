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

-- error in AlgebraicGeometry.PresheafedSpace.HasColimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Auxiliary definition for `PresheafedSpace.colimit_cocone_is_colimit`.
-/
def desc_c_app
(F : «expr ⥤ »(J, PresheafedSpace C))
(s : cocone F)
(U : «expr ᵒᵖ»(opens «expr↥ »(s.X.carrier))) : «expr ⟶ »(s.X.presheaf.obj U, «expr _* »(colimit.desc «expr ⋙ »(F, PresheafedSpace.forget C) ((PresheafedSpace.forget C).map_cocone s), limit (pushforward_diagram_to_colimit F).left_op).obj U) :=
begin
  refine [expr «expr ≫ »(limit.lift _ { X := s.X.presheaf.obj U,
      π := { app := λ j, _, naturality' := λ j j' f, _ } }, (limit_obj_iso_limit_comp_evaluation _ _).inv)],
  { refine [expr «expr ≫ »((s.ι.app (unop j)).c.app U, (F.obj (unop j)).presheaf.map (eq_to_hom _))],
    dsimp [] [] [] [],
    rw ["<-", expr opens.map_comp_obj] [],
    simp [] [] [] [] [] [] },
  { rw [expr PresheafedSpace.congr_app (s.w f.unop).symm U] [],
    dsimp [] [] [] [],
    have [ident w] [] [":=", expr functor.congr_obj (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).map_cocone s) (unop j))) (unop U)],
    simp [] [] ["only"] ["[", expr opens.map_comp_obj_unop, "]"] [] ["at", ident w],
    replace [ident w] [] [":=", expr congr_arg op w],
    have [ident w'] [] [":=", expr nat_trans.congr (F.map f.unop).c w],
    rw [expr w'] [],
    dsimp [] [] [] [],
    simp [] [] [] [] [] [],
    dsimp [] [] [] [],
    simp [] [] [] [] [] [] }
end

-- error in AlgebraicGeometry.PresheafedSpace.HasColimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
theorem desc_c_naturality
(F : «expr ⥤ »(J, PresheafedSpace C))
(s : cocone F)
{U V : «expr ᵒᵖ»(opens «expr↥ »(s.X.carrier))}
(i : «expr ⟶ »(U, V)) : «expr = »(«expr ≫ »(s.X.presheaf.map i, desc_c_app F s V), «expr ≫ »(desc_c_app F s U, «expr _* »(colimit.desc «expr ⋙ »(F, forget C) ((forget C).map_cocone s), (colimit_cocone F).X.presheaf).map i)) :=
begin
  dsimp [] ["[", expr desc_c_app, "]"] [] [],
  ext [] [] [],
  simp [] [] ["only"] ["[", expr limit.lift_π, ",", expr nat_trans.naturality, ",", expr limit.lift_π_assoc, ",", expr eq_to_hom_map, ",", expr assoc, ",", expr pushforward_obj_map, ",", expr nat_trans.naturality_assoc, ",", expr op_map, ",", expr limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc, ",", expr limit_obj_iso_limit_comp_evaluation_inv_π_app, "]"] [] [],
  dsimp [] [] [] [],
  have [ident w] [] [":=", expr functor.congr_hom (congr_arg opens.map (colimit.ι_desc ((PresheafedSpace.forget C).map_cocone s) (unop j))) i.unop],
  simp [] [] ["only"] ["[", expr opens.map_comp_map, "]"] [] ["at", ident w],
  replace [ident w] [] [":=", expr congr_arg quiver.hom.op w],
  rw [expr w] [],
  dsimp [] [] [] [],
  simp [] [] [] [] [] []
end

end ColimitCoconeIsColimit

open ColimitCoconeIsColimit

-- error in AlgebraicGeometry.PresheafedSpace.HasColimits: ././Mathport/Syntax/Translate/Basic.lean:177:17: failed to parenthesize: parenthesize: uncaught backtrack exception
/--
Auxiliary definition for `PresheafedSpace.has_colimits`.
-/ def colimit_cocone_is_colimit (F : «expr ⥤ »(J, PresheafedSpace C)) : is_colimit (colimit_cocone F) :=
{ desc := λ
  s, { base := colimit.desc «expr ⋙ »(F, PresheafedSpace.forget C) ((PresheafedSpace.forget C).map_cocone s),
    c := { app := λ U, desc_c_app F s U, naturality' := λ U V i, desc_c_naturality F s i } },
  fac' := begin
    intros [ident s, ident j],
    dsimp [] [] [] [],
    fapply [expr PresheafedSpace.ext],
    { simp [] [] [] [] [] [] },
    { ext [] [] [],
      dsimp [] ["[", expr desc_c_app, "]"] [] [],
      simp [] [] ["only"] ["[", expr eq_to_hom_op, ",", expr limit.lift_π_assoc, ",", expr eq_to_hom_map, ",", expr assoc, ",", expr pushforward.comp_inv_app, ",", expr limit_obj_iso_limit_comp_evaluation_inv_π_app_assoc, "]"] [] [],
      dsimp [] [] [] [],
      simp [] [] [] [] [] [] }
  end,
  uniq' := λ s m w, begin
    have [ident t] [":", expr «expr = »(m.base, colimit.desc «expr ⋙ »(F, PresheafedSpace.forget C) ((PresheafedSpace.forget C).map_cocone s))] [],
    { apply [expr category_theory.limits.colimit.hom_ext],
      intros [ident j],
      apply [expr continuous_map.ext],
      intros [ident x],
      dsimp [] [] [] [],
      simp [] [] ["only"] ["[", expr colimit.ι_desc_apply, ",", expr map_cocone_ι_app, "]"] [] [],
      rw ["<-", expr w j] [],
      simp [] [] [] [] [] [] },
    fapply [expr PresheafedSpace.ext],
    { exact [expr t] },
    { ext [] [ident U, ident j] [],
      dsimp [] ["[", expr desc_c_app, "]"] [] [],
      simp [] [] ["only"] ["[", expr limit.lift_π, ",", expr eq_to_hom_op, ",", expr eq_to_hom_map, ",", expr assoc, ",", expr limit_obj_iso_limit_comp_evaluation_inv_π_app, "]"] [] [],
      rw [expr PresheafedSpace.congr_app (w (unop j)).symm U] [],
      dsimp [] [] [] [],
      have [ident w] [] [":=", expr congr_arg op (functor.congr_obj (congr_arg opens.map t) (unop U))],
      rw [expr nat_trans.congr (limit.π (pushforward_diagram_to_colimit F).left_op j) w] [],
      simpa [] [] [] [] [] [] }
  end }

/--
When `C` has limits, the category of presheaved spaces with values in `C` itself has colimits.
-/
instance  : has_colimits (PresheafedSpace C) :=
  { HasColimitsOfShape :=
      fun J 𝒥 =>
        by 
          exact
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
          exact
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

